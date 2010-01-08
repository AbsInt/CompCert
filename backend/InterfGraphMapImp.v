Require Import FSets.
Require Import Recdef.
Require Import ZArith.
Require Import Coq.Init.Wf.
Require Import FSetInterface.
Require Import SetsFacts.
Require Import FMaps.
Require Import OrderedOption.
Require Import FMapAVL.
Require Import Edges.
Require Import MyRegisters.

Module Register := Regs.

Import Edge.

Module VertexSet := FSetAVL.Make Vertex.
Module EdgeSet := FSetAVL.Make Edge.
Module VertexMap := FMapAVL.Make Vertex.
Module MapFacts := Facts VertexMap.
Module RegFacts := MyFacts VertexSet.
Module MEdgeFacts := MyFacts EdgeSet.
Module RegRegProps := MEdgeFacts.Props.
Module Props := RegFacts.Props.

Definition adj_set x m :=
match (VertexMap.find x m) with
| None => VertexSet.empty
| Some x => x
end.

Record tt : Type := Make_Graph {
vertices : VertexSet.t;
imap : VertexMap.t VertexSet.t;
pmap : VertexMap.t VertexSet.t;
extremities_imap : forall x, VertexMap.In x imap <-> VertexSet.In x vertices;
extremities_pmap : forall x, VertexMap.In x pmap <-> VertexSet.In x vertices;
simple_graph : forall x y, VertexSet.In x (adj_set y imap) /\
                           VertexSet.In x (adj_set y pmap) -> False;
sym_imap : forall x y, VertexSet.In x (adj_set y imap) ->
                       VertexSet.In y (adj_set x imap);
sym_pmap : forall x y, VertexSet.In x (adj_set y pmap) ->
                       VertexSet.In y (adj_set x pmap);
not_eq_extremities : forall x y, VertexSet.In x (adj_set y imap) \/
                                 VertexSet.In x (adj_set y pmap) ->
                                 ~Vertex.eq x y
}.

Definition t := tt.

Definition V := vertices.

Definition edgemap_to_edgeset map w :=
VertexMap.fold
   (fun y imapy s => VertexSet.fold
                     (fun z s' => EdgeSet.add (y,z,w) s')
                     imapy
              s)
   map
   EdgeSet.empty.

Definition AE g := edgemap_to_edgeset (pmap g) (Some N0).

Definition IE g := edgemap_to_edgeset (imap g) None.

Definition is_precolored v (g : t) := is_mreg v.

Definition imap_remove m x :=
VertexMap.remove x
(VertexSet.fold
  (fun y => VertexMap.add y (VertexSet.remove x (adj_set y m)))
  (adj_set x m)
  m
).

Lemma change_fst : forall x y z,
fst_ext (x,y,z) = x.

Proof.
auto.
Qed.

Lemma change_snd : forall x y z,
snd_ext (x,y,z) = y.

Proof.
auto.
Qed.

Lemma change_weight : forall x y z,
get_weight (x,y,z) = z.

Proof.
auto.
Qed.

(* rewriting tactic *)

Ltac change_rewrite :=
repeat (try rewrite change_fst in *;try rewrite change_snd in *;try rewrite change_weight in *).

(* two tactics for proving equality of edges *)

Ltac Eq_eq :=
apply eq_ordered_eq;unfold E.eq;split;[simpl;split;intuition|simpl;apply OptionN_as_OT.eq_refl].

Ltac Eq_comm_eq := rewrite edge_comm;Eq_eq.

Lemma eq_charac : forall x y,
eq x y -> (Vertex.eq (fst_ext x) (fst_ext y) /\ Vertex.eq (snd_ext x) (snd_ext y)) \/
               (Vertex.eq (fst_ext x) (snd_ext y) /\ Vertex.eq (snd_ext x) (fst_ext y)).

Proof.
intros x y H;unfold eq in H;unfold ordered_edge in H;
unfold get_edge in H.
destruct (OTFacts.lt_dec (snd_ext x) (fst_ext x));
destruct (OTFacts.lt_dec (snd_ext y) (fst_ext y));
unfold E.eq in H;simpl in H;intuition.
Qed.

Section fold_assoc_interf_map.

Variable A : Type.

Inductive eq_set_option : option VertexSet.t -> option VertexSet.t -> Prop :=
|None_eq : eq_set_option None None
|Some_eq : forall s s', VertexSet.Equal s s' -> eq_set_option (Some s) (Some s').

Definition EqualSetMap m1 m2 := forall x, eq_set_option (VertexMap.find x m1) (VertexMap.find x m2).

Lemma EqualSetMap_refl : forall m, EqualSetMap m m.

Proof.
unfold EqualSetMap. intro m. intro x.
destruct (VertexMap.find x m).
constructor. intuition.
constructor.
Qed.

Lemma EqualSetMap_trans : forall m1 m2 m3,
EqualSetMap m1 m2 ->
EqualSetMap m2 m3 ->
EqualSetMap m1 m3.

Proof.
intros m1 m2 m3 H H0.
unfold EqualSetMap in *.
intro x.
generalize (H x). clear H. intro H.
generalize (H0 x). clear H0. intro H0.
destruct (VertexMap.find x m1).
inversion H. subst.
rewrite <-H2 in H0.
destruct (VertexMap.find x m3).
constructor. inversion H0. subst.
rewrite H3. assumption.
inversion H0.
destruct (VertexMap.find x m3).
inversion H0. inversion H. subst. rewrite <-H4 in H1. inversion H1.
constructor.
Qed.

Lemma fold_left_compat_map : forall (f : VertexMap.t VertexSet.t -> A -> VertexMap.t VertexSet.t) l e e',
EqualSetMap e e' ->
(forall e1 e2 a, EqualSetMap e1 e2 -> EqualSetMap (f e1 a) (f e2 a)) ->
EqualSetMap (fold_left f l e) (fold_left f l e').

Proof.
intro f;induction l;simpl.
auto.
intros e e' H H0 H1.
apply (IHl (f e a) (f e' a)).
apply H0;assumption.
assumption.
Qed.

Lemma fold_left_assoc_map : forall l (f : VertexMap.t VertexSet.t -> A -> VertexMap.t VertexSet.t) x h,
(forall (y z : A) s, EqualSetMap (f (f s y) z) (f (f s z) y)) ->
(forall e1 e2 a, EqualSetMap e1 e2 -> EqualSetMap (f e1 a) (f e2 a)) ->
EqualSetMap (fold_left f (h :: l) x) (f (fold_left f l x) h).

Proof.
induction l;simpl;intros f x h H H0.
apply EqualSetMap_refl.
apply EqualSetMap_trans with (m2 := fold_left f (h :: l) (f x a)).
simpl. apply fold_left_compat_map. apply H.
assumption.
apply IHl. assumption. assumption.
Qed.

End fold_assoc_interf_map.

Lemma fold_assoc : forall g g' y0 z s,
(forall x y a, EdgeSet.Equal (g x (g' y a)) (g' y (g x a))) ->
(forall (y z0 : VertexSet.elt) (s0 : EdgeSet.t),
EdgeSet.Equal (g z0 (g y s0)) (g y (g z0 s0))) ->
(forall (e1 e2 : EdgeSet.t) (a1 : VertexSet.elt),
EdgeSet.Equal e1 e2 -> EdgeSet.Equal (g a1 e1) (g a1 e2)) ->
(forall (e1 e2 : EdgeSet.t) (a1 : VertexSet.elt),
EdgeSet.Equal e1 e2 -> EdgeSet.Equal (g' a1 e1) (g' a1 e2)) ->
(forall (y z0 : VertexSet.elt) (s0 : EdgeSet.t),
EdgeSet.Equal (g' z0 (g' y s0)) (g' y (g' z0 s0))) ->
EdgeSet.Equal (VertexSet.fold g z (VertexSet.fold g' y0 s))
              (VertexSet.fold g' y0 (VertexSet.fold g z s)).

Proof.
intros.
repeat rewrite VertexSet.fold_1.
set (f1 := fun (a : EdgeSet.t) (e : VertexSet.elt) => g e a).
set (f2 := fun (a : EdgeSet.t) (e : VertexSet.elt) => g' e a).
induction (VertexSet.elements z). simpl.
apply EdgeSet.eq_refl.

set (l' := VertexSet.elements y0) in *.
assert (EdgeSet.Equal (fold_left f2 l' (fold_left f1 (a :: l) s))
                      (fold_left f2 l' (f1 (fold_left f1 l s) a))).
apply MEdgeFacts.fold_left_compat_set.
apply MEdgeFacts.fold_left_assoc.

unfold f2. assumption.
unfold f2. assumption.
unfold f1. assumption.

apply EdgeSet.eq_trans with (s' := (fold_left f2 l' (f1 (fold_left f1 l s) a))).
set (s' := fold_left f1 l s) in *.
cut (EdgeSet.Equal (fold_left f2 l' (f1 s' a)) (f1 (fold_left f2 l' s') a)).
intro.
apply EdgeSet.eq_trans with (s' := f1 (fold_left f2 l' s') a).
rewrite MEdgeFacts.fold_left_assoc.
apply H1. assumption.
assumption.
assumption.
apply EdgeSet.eq_sym. auto.

clear IHl. clear H4.
induction l'. simpl. apply EdgeSet.eq_refl.
assert (EdgeSet.Equal (f1 (fold_left f2 (a0 :: l') s') a)
                      (f1 (f2 (fold_left f2 l' s') a0) a)).
apply H1.
apply MEdgeFacts.fold_left_assoc.
assumption.
assumption.
apply EdgeSet.eq_trans with (s':= (f1 (f2 (fold_left f2 l' s') a0) a)).
rewrite MEdgeFacts.fold_left_assoc.
apply EdgeSet.eq_trans with (s' := f2 (f1 (fold_left f2 l' s') a) a0).
apply H2. assumption.
unfold f1. unfold f2.
unfold EdgeSet.eq. apply EdgeSet.eq_sym.
apply H.
assumption.
assumption.
apply H1. apply EdgeSet.eq_sym. apply MEdgeFacts.fold_left_assoc.
assumption.
assumption.
apply EdgeSet.eq_sym. auto.
Qed.

Lemma edgemap_to_edgeset_charac : forall m x y (w : option N),
(forall a b, VertexSet.In a (adj_set b m) ->
             VertexSet.In b (adj_set a m)) ->
(EdgeSet.In (x,y,w) (edgemap_to_edgeset m w) <-> VertexSet.In y (adj_set x m)).

Proof.
intros m x y w Hsym. split; intros.
unfold edgemap_to_edgeset in H.
rewrite VertexMap.fold_1 in H.
generalize VertexMap.elements_2. intro.
generalize (H0 _ m). clear H0. intro HH.
induction (VertexMap.elements m).
simpl in H.
elim (EdgeSet.empty_1 H).
set (f := (fun (a : EdgeSet.t) (p : VertexMap.key * VertexSet.t) =>
          VertexSet.fold
            (fun (z : VertexSet.elt) (s' : EdgeSet.t) =>
             EdgeSet.add (fst p, z, w) s') (snd p) a)) in *.
case_eq a; intros; subst.
rewrite MEdgeFacts.fold_left_assoc in H.
set (s := fold_left f l EdgeSet.empty) in *.
unfold f in H. simpl in H.
assert (EdgeSet.In (x,y,w) s \/ (VertexSet.In y t0 /\ Vertex.eq k x) \/ 
       (VertexSet.In x t0 /\ Vertex.eq k y)).
clear IHl. intros.
rewrite VertexSet.fold_1 in H.
generalize VertexSet.elements_2.
intro H0. generalize (H0 t0). clear H0. intro Helt.
induction (VertexSet.elements t0).
simpl in H. left. assumption.
rewrite MEdgeFacts.fold_left_assoc in H.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H).
fold (eq (k,a,w) (x,y,w)) in H0.
right.
destruct (eq_charac _ _ H0); destruct H1; change_rewrite.
left. split.
apply Helt. left. apply Vertex.eq_sym. assumption.
assumption.
right. split.
apply Helt. left. apply Vertex.eq_sym. assumption.
assumption.
apply IHl0. assumption.
intros. apply Helt. right. assumption.

intros. apply RegRegProps.add_add.
intros. apply RegRegProps.Dec.F.add_m. apply eq_refl. assumption.

destruct H0.
apply IHl.
assumption.
intros. apply HH. auto.
destruct H0.
assert (VertexMap.MapsTo x t0 m).
apply HH.
left.
constructor; simpl; intuition.
generalize (VertexMap.find_1 H1). clear H1. intro H1.
unfold adj_set. rewrite H1. intuition.
apply Hsym.
assert (VertexMap.MapsTo y t0 m).
apply HH.
left.
constructor; simpl; intuition.
generalize (VertexMap.find_1 H1). clear H1. intro H1.
unfold adj_set. rewrite H1. intuition.

unfold f.
intros. set (g := (fun (z0 : VertexSet.elt) (s' : EdgeSet.t) =>
      EdgeSet.add (fst z, z0, w) s')).
set (g' :=  fun (z0 : VertexSet.elt) (s' : EdgeSet.t) =>
      EdgeSet.add (fst y0, z0, w) s').
apply fold_assoc.
unfold g. unfold g'.
intros. apply RegRegProps.add_add.
unfold g. unfold g'.
intros. apply RegRegProps.add_add.
intros. apply RegRegProps.Dec.F.add_m. apply eq_refl. assumption.
intros. apply RegRegProps.Dec.F.add_m. apply eq_refl. assumption.
unfold g. unfold g'.
intros. apply RegRegProps.add_add.
intros.
unfold f.
rewrite VertexSet.fold_1.
rewrite VertexSet.fold_1.
apply MEdgeFacts.fold_left_compat_set.
assumption.
intros. apply RegRegProps.Dec.F.add_m. apply eq_refl. assumption.

unfold edgemap_to_edgeset.
rewrite VertexMap.fold_1.
generalize VertexMap.elements_1. intro.
case_eq (VertexMap.find x m); intros.
generalize (H0 _ m x t0). clear H0. intro HH.
induction (VertexMap.elements m).
simpl.
assert (VertexMap.MapsTo x t0 m).
apply VertexMap.find_2. assumption.
generalize (HH H0). intro H2. inversion H2.

set (f := (fun (a : EdgeSet.t) (p : VertexMap.key * VertexSet.t) =>
          VertexSet.fold
            (fun (z : VertexSet.elt) (s' : EdgeSet.t) =>
             EdgeSet.add (fst p, z, w) s') (snd p) a)) in *.
rewrite MEdgeFacts.fold_left_assoc.
set (s := fold_left f l EdgeSet.empty) in *.
unfold f.
destruct a. simpl.
rewrite VertexSet.fold_1.
generalize VertexSet.elements_1.
intro H2. generalize (H2 t1 y). clear H2. intro HHH.
induction (VertexSet.elements t1). simpl.
assert (VertexMap.MapsTo x t0 m).
apply VertexMap.find_2. assumption.
generalize (HH H0). intro H2.
inversion H2; subst.
inversion H4. simpl in H3. simpl in H5. subst.
unfold adj_set in H. rewrite H1 in H.
generalize (HHH H). intro. inversion H5.
apply IHl. intro. auto.

rewrite MEdgeFacts.fold_left_assoc.
generalize (VertexMap.find_2 H1). intro.
generalize (HH H0). clear HH H0. intro HH.
inversion HH; subst.
inversion H2; simpl in *; subst. clear H2 HH.
destruct (Vertex.eq_dec y a).
apply EdgeSet.add_1.
Eq_eq.
apply EdgeSet.add_2.
apply IHl0.
intro H2. generalize (HHH H2). clear HHH H2. intro H2.
inversion H2. subst.
elim (n H4).
assumption.
apply EdgeSet.add_2.
assert (forall l', EdgeSet.In (x,y,w) s -> 
        EdgeSet.In (x, y, w)
                   (fold_left
                   (fun (a0 : EdgeSet.t) (e : VertexSet.elt) => EdgeSet.add (k, e, w) a0)
                   l' s)).
clear H HH H1 H2 IHl IHl0 HHH Hsym.
intros.
induction l'. simpl. assumption.
rewrite MEdgeFacts.fold_left_assoc.
destruct (Edge.eq_dec (k,a0,w) (x,y,w)).
apply EdgeSet.add_1. auto.
apply EdgeSet.add_2. apply IHl'.

intros. apply RegRegProps.add_add.
intros. apply RegRegProps.Dec.F.add_m. apply eq_refl. assumption.

apply H0.
apply IHl.
auto.

intros. apply RegRegProps.add_add.
intros. apply RegRegProps.Dec.F.add_m. apply eq_refl. assumption.

unfold f.
intros. set (g := (fun (z0 : VertexSet.elt) (s' : EdgeSet.t) =>
      EdgeSet.add (fst z, z0, w) s')).
set (g' :=  fun (z0 : VertexSet.elt) (s' : EdgeSet.t) =>
      EdgeSet.add (fst y0, z0, w) s').
apply fold_assoc.
unfold g. unfold g'.
intros. apply RegRegProps.add_add.
unfold g. unfold g'.
intros. apply RegRegProps.add_add.
intros. apply RegRegProps.Dec.F.add_m. apply eq_refl. assumption.
intros. apply RegRegProps.Dec.F.add_m. apply eq_refl. assumption.
unfold g. unfold g'.
intros. apply RegRegProps.add_add.
intros.
unfold f.
rewrite VertexSet.fold_1.
rewrite VertexSet.fold_1.
apply MEdgeFacts.fold_left_compat_set.
assumption.
intros. apply RegRegProps.Dec.F.add_m. apply eq_refl. assumption.

unfold adj_set in H. rewrite H1 in H. elim (VertexSet.empty_1 H).
Qed.

Require Import FMapFacts.

Module InterfFacts := FMapFacts.Facts VertexMap.

Lemma imap_remove_1 : forall x y m r,
~Vertex.eq r x ->
~Vertex.eq r y ->
VertexSet.In x (adj_set y m) ->
VertexSet.In x (adj_set y (imap_remove m r)).

Proof.
intros.
unfold imap_remove.
unfold adj_set.
cut (VertexSet.In x match
  (VertexMap.find (elt:=VertexSet.t) y
     (VertexMap.remove (elt:=VertexSet.t) r
        (VertexSet.fold
           (fun y0 : VertexSet.elt =>
            VertexMap.add y0 (VertexSet.remove r (adj_set y0 m)))
           (adj_set r m) m))) with
  | Some x0 => x0
  | None => VertexSet.empty
end); auto.
rewrite MapFacts.remove_neq_o.

rewrite VertexSet.fold_1.
induction (VertexSet.elements (adj_set r m)); intros.
simpl. assumption.

set (f:= (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
                VertexMap.add e (VertexSet.remove r (adj_set e m)) a)) in *.
assert (EqualSetMap (fold_left f (a :: l) m) (f (fold_left f l m) a)).
apply fold_left_assoc_map.
intros.
unfold f. unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.remove_m. apply Vertex.eq_refl.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_trans (Vertex.eq_sym e) e0)).
apply VertexSet.eq_refl. apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.remove_m. apply Vertex.eq_refl.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.remove_m. apply Vertex.eq_refl.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.

rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s); constructor; auto.
apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

intros.
unfold f.
unfold EqualSetMap.
intros.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Vertex.eq_sym. assumption.
apply Vertex.eq_sym. assumption.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H2. auto. auto.
unfold EqualSetMap in H2.
generalize (H2 y). intro H3.
case_eq (VertexMap.find y (fold_left f (a :: l) m)); intros.
rewrite H4 in H3. inversion H3. subst.
unfold f in H6.
destruct (Vertex.eq_dec y a).
rewrite MapFacts.add_eq_o in H6. inversion H6.
rewrite H7. rewrite H8. apply VertexSet.remove_2.
auto. unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e)). assumption.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H6.
rewrite H7. unfold f in IHl.
case_eq (VertexMap.find (elt:=VertexSet.t) y
       (fold_left
          (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
           VertexMap.add e (VertexSet.remove r (adj_set e m)) a) l m)); intros;
rewrite H5 in *.
inversion H6. subst.
assumption.
inversion H6.
auto.
rewrite H4 in H3. inversion H3. subst.
unfold f in H5.
destruct (Vertex.eq_dec y a).
rewrite MapFacts.add_eq_o in H5.
inversion H5.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H5.
unfold f in IHl.
case_eq (VertexMap.find (elt:=VertexSet.t) y
       (fold_left
          (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
           VertexMap.add e (VertexSet.remove r (adj_set e m)) a) l m)); intros;
rewrite H6 in *.
inversion H5.
assumption.
auto.
auto.
Qed.

Lemma imap_remove_2 : forall x y m r,
Vertex.eq r x \/ Vertex.eq r y ->
(forall a b, VertexSet.In a (adj_set b m) ->
             VertexSet.In b (adj_set a m)) ->
~VertexSet.In x (adj_set y (imap_remove m r)).

Proof.
intros x y m r H HH.
unfold imap_remove.
unfold adj_set.
cut (~VertexSet.In x match
  (VertexMap.find (elt:=VertexSet.t) y
     (VertexMap.remove (elt:=VertexSet.t) r
        (VertexSet.fold
           (fun y0 : VertexSet.elt =>
            VertexMap.add y0 (VertexSet.remove r (adj_set y0 m)))
           (adj_set r m) m))) with
  | Some x0 => x0
  | None => VertexSet.empty
end); auto.
destruct (Vertex.eq_dec r y).
rewrite MapFacts.remove_eq_o.
apply VertexSet.empty_1.
assumption.
rewrite MapFacts.remove_neq_o.
destruct H.

generalize VertexSet.elements_1. intro HHH.
generalize (HHH (adj_set r m) y). clear HHH. intro HHH.
rewrite VertexSet.fold_1.
induction (VertexSet.elements (adj_set r m)); intros.
simpl. intro H0.
generalize (HH _ _ H0). intro H1.
assert (InA Vertex.eq y nil).
apply HHH.
unfold adj_set. rewrite (MapFacts.find_o _ H). assumption.
inversion H2.

set (f:= (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
                VertexMap.add e (VertexSet.remove r (adj_set e m)) a)) in *.
assert (EqualSetMap (fold_left f (a :: l) m) (f (fold_left f l m) a)).
apply fold_left_assoc_map.
intros.
unfold f. unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.remove_m. apply Vertex.eq_refl.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_trans (Vertex.eq_sym e) e0)).
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.remove_m. apply Vertex.eq_refl.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.remove_m. apply Vertex.eq_refl.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s); constructor; auto.
apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

intros.
unfold f.
unfold EqualSetMap.
intros.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Vertex.eq_sym. assumption.
apply Vertex.eq_sym. assumption.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H0. auto. auto.

unfold EqualSetMap in H0.
generalize (H0 y). intro H1.
case_eq (VertexMap.find y (fold_left f (a :: l) m)); intros.
rewrite H2 in H1. inversion H1. subst.
unfold f in H4.
destruct (Vertex.eq_dec y a).
rewrite MapFacts.add_eq_o in H4. inversion H4.
rewrite H5. rewrite H6. apply VertexSet.remove_1. auto. apply Regs.eq_sym. auto.

rewrite MapFacts.add_neq_o in H4.
rewrite H5. unfold f in IHl.
case_eq (VertexMap.find (elt:=VertexSet.t) y
       (fold_left
          (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
           VertexMap.add e (VertexSet.remove r (adj_set e m)) a) l m)); intros;
rewrite H3 in *.
inversion H4. subst.
apply IHl.
intros; intuition.
inversion H7; subst.
elim (n0 H9). assumption.
inversion H4.
auto.
apply VertexSet.empty_1.
elim (n H).
auto.
Qed.

Lemma imap_remove_3 : forall x y m r,
VertexSet.In x (adj_set y (imap_remove m r)) ->
VertexSet.In x (adj_set y m).

Proof.
intros.
assert (VertexSet.In x match
  (VertexMap.find (elt:=VertexSet.t) y
     (VertexMap.remove (elt:=VertexSet.t) r
        (VertexSet.fold
           (fun y0 : VertexSet.elt =>
            VertexMap.add y0 (VertexSet.remove r (adj_set y0 m)))
           (adj_set r m) m))) with
  | Some x0 => x0
  | None => VertexSet.empty
end) by auto. generalize H0. clear H H0. intro H.
destruct (Vertex.eq_dec y r).
rewrite MapFacts.remove_eq_o in H.
elim (VertexSet.empty_1 H). apply Regs.eq_sym. auto.
rewrite MapFacts.remove_neq_o in H.
unfold adj_set.
rewrite VertexSet.fold_1 in H.

generalize VertexSet.elements_2. intro.
generalize (H0 (adj_set y m) x). clear H0. intro HH.

induction (VertexSet.elements (adj_set r m)). simpl in H. assumption.

set (f:= (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
                VertexMap.add e (VertexSet.remove r (adj_set e m)) a)) in *.
assert (EqualSetMap (fold_left f (a :: l) m) (f (fold_left f l m) a)).
apply fold_left_assoc_map.
intros.
unfold f. unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.remove_m. apply Vertex.eq_refl.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_trans (Vertex.eq_sym e) e0)).
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.remove_m. apply Vertex.eq_refl.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.remove_m. apply Vertex.eq_refl.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s); constructor; auto.
apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

intros.
unfold f.
unfold EqualSetMap.
intros.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Vertex.eq_sym. assumption.
apply Vertex.eq_sym. assumption.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H0. auto. auto.

unfold EqualSetMap in H0.
generalize (H0 y).
case_eq (VertexMap.find y (fold_left f (a :: l) m)); intros.
rewrite H1 in *. inversion H2. subst.
unfold f in H4.
destruct (Vertex.eq_dec y a).
rewrite MapFacts.add_eq_o in H4.
apply HH.
apply VertexSet.elements_1.
unfold adj_set. rewrite (MapFacts.find_o _ e). fold (adj_set a m).
apply VertexSet.remove_3 with (x:=r).
inversion H4. subst. rewrite <-H5. assumption.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H4.
fold f in H4. rewrite <-H4 in IHl.
apply IHl.
rewrite <-H5. assumption.
auto.

inversion H2. subst. rewrite <-H3 in *. rewrite H1 in *.
elim (VertexSet.empty_1 H).
auto.
Qed.

Lemma imap_remove_4 : forall x m r,
VertexMap.In x (imap_remove m r) ->
(forall a b, VertexSet.In a (adj_set b m) ->
             VertexSet.In b (adj_set a m)) ->
VertexMap.In x m.

Proof.
intros x m r H Hsym.
unfold imap_remove in H.
destruct (Vertex.eq_dec x r).
elim (VertexMap.remove_1 (Vertex.eq_sym e) H).
apply (proj2 (MapFacts.in_find_iff _ _)).
generalize (proj1 (MapFacts.in_find_iff _ _) H). clear H. intro H.
rewrite MapFacts.remove_neq_o in H.
rewrite VertexSet.fold_1 in H. intro H0. elim H. clear H.

generalize VertexSet.elements_2. intro.
generalize (H (adj_set r m) x). clear H. intro HH.

induction (VertexSet.elements (adj_set r m)). simpl.
assumption.

set (f:= (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
                VertexMap.add e (VertexSet.remove r (adj_set e m)) a)) in *.
assert (EqualSetMap (fold_left f (a :: l) m) (f (fold_left f l m) a)).
apply fold_left_assoc_map.
intros.
unfold f. unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.remove_m. apply Vertex.eq_refl.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_trans (Vertex.eq_sym e) e0)).
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.remove_m. apply Vertex.eq_refl.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.remove_m. apply Vertex.eq_refl.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s); constructor; auto.
apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

intros.
unfold f.
unfold EqualSetMap.
intros.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Vertex.eq_sym. assumption.
apply Vertex.eq_sym. assumption.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H. auto. auto.

generalize (H x). clear H. intro H.
case_eq (VertexMap.find x (fold_left f (a :: l) m)); intros.
rewrite H1 in H. inversion H. subst.
unfold f in H3.
destruct (Vertex.eq_dec x a).
assert (VertexSet.In r (adj_set x m)).
apply Hsym. apply HH. left. auto.
unfold adj_set in H2. rewrite H0 in H2. elim (VertexSet.empty_1 H2).
rewrite MapFacts.add_neq_o in H3.
fold f in H3.
assert (VertexMap.find x (fold_left f l m) = None).
apply IHl. 
intro. apply HH. auto.
rewrite H2 in H3. inversion H3.
auto.
reflexivity.
auto.
Qed.

Lemma imap_remove_5 : forall r x m,
VertexMap.In x m ->
~Vertex.eq x r ->
VertexMap.In x (imap_remove m r).

Proof.
intros.
unfold imap_remove.
rewrite MapFacts.in_find_iff.
rewrite MapFacts.remove_neq_o.
rewrite VertexSet.fold_1.
set (f := (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
      VertexMap.add e (VertexSet.remove r (adj_set e m)) a)).
induction (VertexSet.elements (adj_set r m)). simpl.
rewrite MapFacts.in_find_iff in H. assumption.

cut (VertexMap.find x (f (fold_left f l m) a) <> None).
intro H1.
cut (EqualSetMap (fold_left f (a :: l) m) (f (fold_left f l m) a)). intro H2.
generalize (H2 x). clear H2. intro H2. inversion H2.
simpl. rewrite <-H4 in *. rewrite <-H5 in *. assumption.
simpl. rewrite <-H3 in *. congruence.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f. intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.remove_m. apply Vertex.eq_refl.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_trans (Vertex.eq_sym e) e0)).
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.remove_m. apply Vertex.eq_refl.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.remove_m. apply Vertex.eq_refl.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s); constructor; auto.
apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

intros.
unfold f.
unfold EqualSetMap.
intros.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Vertex.eq_sym. assumption.
apply Vertex.eq_sym. assumption.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H2. auto. auto.

set (tmp := fold_left f l m) in *.
unfold f.
destruct (Vertex.eq_dec x a).
rewrite MapFacts.add_eq_o. congruence.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
assumption.
auto.
auto.
Qed.

Lemma extremities_in_remove_vertex_imap v g :
forall x,
VertexMap.In x (imap_remove (imap g) v) <->
VertexSet.In x (VertexSet.remove v (V g)).

Proof.
split; intros.
apply VertexSet.remove_2.
unfold imap_remove in H. 
intro Helim; apply (VertexMap.remove_1 Helim H).
apply (extremities_imap g x); apply imap_remove_4 with (r:=v); try assumption.
exact (sym_imap g).

generalize (proj2 (extremities_imap g x)). intro.
generalize (H0 (VertexSet.remove_3 H)). clear H0. intro H0.
apply imap_remove_5. assumption.
intro H1. elim (VertexSet.remove_1 (Vertex.eq_sym H1) H).
Qed.

Lemma extremities_in_remove_vertex_pmap v g :
forall x,
VertexMap.In x (imap_remove (pmap g) v) <->
VertexSet.In x (VertexSet.remove v (V g)).

Proof.
split; intros.
apply VertexSet.remove_2.
unfold imap_remove in H. 
intro Helim; apply (VertexMap.remove_1 Helim H).
apply (extremities_pmap g x); apply imap_remove_4 with (r:=v); try assumption.
exact (sym_pmap g).

generalize (proj2 (extremities_pmap g x)). intro.
generalize (H0 (VertexSet.remove_3 H)). clear H0. intro H0.
apply imap_remove_5. assumption.
intro H1. elim (VertexSet.remove_1 (Vertex.eq_sym H1) H).
Qed.

Lemma simple_graph_remove_vertex_map v g :
forall x y,
VertexSet.In x (adj_set y (imap_remove (imap g) v)) /\
VertexSet.In x (adj_set y (imap_remove (pmap g) v)) ->
False.

Proof.
intros.
apply (simple_graph g x y).
destruct H.
generalize (imap_remove_3 _ _ _ _ H).
generalize (imap_remove_3 _ _ _ _ H0).
auto.
Qed.

Lemma not_eq_extremities_remove_vertex_map v g : forall x y,
VertexSet.In x (adj_set y (imap_remove (imap g) v)) \/
VertexSet.In x (adj_set y (imap_remove (pmap g) v)) ->
~Vertex.eq x y.

Proof.
intros.
apply (not_eq_extremities g).
destruct H;[left|right]; apply (imap_remove_3 _ _ _ _ H).
Qed.

Lemma sym_imap_remove_vertex v g :
forall (x : VertexSet.elt) (y : VertexMap.key),
VertexSet.In x (adj_set y (imap_remove (imap g) v)) ->
VertexSet.In y (adj_set x (imap_remove (imap g) v)).

Proof.
intros.
generalize (imap_remove_2 x y (imap g) v). intro H0.
apply imap_remove_1.
intro H1. elim (H0 (or_intror _ H1) (sym_imap g) H).
intro H1. elim (H0 (or_introl _ H1) (sym_imap g) H).
generalize (imap_remove_3 _ _ _ _ H). intro H1.
apply (sym_imap g). assumption.
Qed.

Lemma sym_pmap_remove_vertex v g :
forall (x : VertexSet.elt) (y : VertexMap.key),
VertexSet.In x (adj_set y (imap_remove (pmap g) v)) ->
VertexSet.In y (adj_set x (imap_remove (pmap g) v)).

Proof.
intros.
generalize (imap_remove_2 x y (pmap g) v). intro H0.
apply imap_remove_1.
intro H1. elim (H0 (or_intror _ H1) (sym_pmap g) H).
intro H1. elim (H0 (or_introl _ H1) (sym_pmap g) H).
generalize (imap_remove_3 _ _ _ _ H). intro H1.
apply (sym_pmap g). assumption.
Qed.

Definition remove_vertex v g :=
Make_Graph (VertexSet.remove v (V g)) 
           (imap_remove (imap g) v)
           (imap_remove (pmap g) v)
           (extremities_in_remove_vertex_imap v g)
           (extremities_in_remove_vertex_pmap v g)
           (simple_graph_remove_vertex_map v g)
           (sym_imap_remove_vertex v g)
           (sym_pmap_remove_vertex v g)
           (not_eq_extremities_remove_vertex_map v g).

Definition map_merge e map :=
let adj_snd := VertexSet.remove (fst_ext e) (adj_set (snd_ext e) map) in
let adj_fst := VertexSet.remove (snd_ext e) (adj_set (fst_ext e) map) in
let new_fst_adj := VertexSet.union adj_fst adj_snd in
(*
let new_fst_adj_ := VertexSet.union (adj_set (fst_ext e) map) (adj_set (snd_ext e) map) in
let new_fst_adj := VertexSet.remove (fst_ext e) (VertexSet.remove (snd_ext e) new_fst_adj_) in
let m := VertexMap.add (fst_ext e) new_fst_adj map in
*)
let redirect_m := 
  VertexSet.fold 
   (fun y m' => 
     VertexMap.add y 
      (VertexSet.add (fst_ext e) (VertexSet.remove (snd_ext e) (adj_set y map))) m') 
      adj_snd
(*
   (VertexSet.remove (fst_ext e) (adj_set (snd_ext e) m))
*)
   map in
VertexMap.remove (snd_ext e)
(VertexMap.add (fst_ext e) new_fst_adj redirect_m).

Definition imap_merge e g := map_merge e (imap g).

Definition resolve_conflicts y pm padj iadj :=
let m' := VertexSet.fold 
            (fun x m => VertexMap.add x (VertexSet.remove y (adj_set x pm)) m)
            (VertexSet.inter padj iadj)
            pm
in VertexMap.add y (VertexSet.diff padj iadj) m'.

Definition pmap_merge e g im :=
let pm := map_merge e (pmap g) in
resolve_conflicts (fst_ext e) pm (adj_set (fst_ext e) pm) (adj_set (fst_ext e) im).

Definition In_graph_edge e g :=
EdgeSet.In e (AE g) \/ EdgeSet.In e (IE g).

Lemma In_graph_edge_dec : forall e g,
{In_graph_edge e g}+{~In_graph_edge e g}.

Proof.
intros e g.
destruct (RegRegProps.In_dec e (AE g)).
left. left. assumption.
destruct (RegRegProps.In_dec e (IE g)).
left. right. assumption.
right. intro H. destruct H;[elim n|elim n0];assumption.
Qed.

Lemma aff_edge_dec : forall e,
{aff_edge e}+{~aff_edge e}.

Proof.
intro e.
case_eq (get_weight e).
intros n H. left. unfold aff_edge. exists n. auto.
intro H. right. intro H0. unfold aff_edge in H0.
destruct H0 as [w H0]. rewrite H0 in H. inversion H.
Qed.

Definition In_graph (v : Vertex.t) g := VertexSet.In v (V g).

Add Morphism get_weight : get_weight_m.

Proof.
intros x y H.
rewrite (weight_ordered_weight x);rewrite (weight_ordered_weight y).
unfold get_weight;unfold E.eq in H.
destruct H as [_ H];inversion H;[|rewrite H2];reflexivity.
Qed.

Lemma E_weights_aux : forall e map w s,
EdgeSet.In e 
(VertexMap.fold 
   (fun y imapy s => VertexSet.fold 
                     (fun z s' => EdgeSet.add (y,z,w) s')
                     imapy 
              s) 
   map 
   s) ->
EdgeSet.In e s \/ get_weight e = w.

Proof.
intros.
rewrite VertexMap.fold_1 in H.
generalize H. clear H. generalize (VertexMap.elements map) s.
induction l.
simpl. auto.
intros. simpl in H.
set (s' := VertexSet.fold
            (fun (z : VertexSet.elt) (s' : EdgeSet.t) =>
             EdgeSet.add (fst a, z, w) s') (snd a) s0) in H.
generalize (IHl s' H). intro H0.
destruct H0.
unfold s' in H0.

assert (EdgeSet.In e (VertexSet.fold (fun (z : VertexSet.elt) (s' : EdgeSet.t) =>
        EdgeSet.add (fst a, z, w) s') (snd a) s0) -> EdgeSet.In e s0 \/ get_weight e = w).
clear H IHl.
rewrite VertexSet.fold_1.
induction (VertexSet.elements (snd a)).
simpl. auto.
rewrite MEdgeFacts.fold_left_assoc.
intro H1. destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H1).
fold (eq (fst a, a0, w) e) in H.
right. rewrite <-H. simpl. reflexivity.
apply IHl0. assumption.

intros. apply RegRegProps.add_add.
intros. apply RegRegProps.Dec.F.add_m.
apply eq_refl.
assumption.
apply H1. assumption.
right. assumption.
Qed.

Lemma E_weights : forall e m w,
EdgeSet.In e (edgemap_to_edgeset m w) -> get_weight e = w.

Proof.
intros.
generalize (E_weights_aux e m w EdgeSet.empty). intro H0.
destruct H0.
assumption.
elim (EdgeSet.empty_1 H0).
assumption.
Qed.

Lemma IE_weights : forall g e,
EdgeSet.In e (IE g) -> get_weight e = None.

Proof.
unfold IE. intros. eapply E_weights. eassumption.
Qed.

Lemma AE_weights : forall g e,
EdgeSet.In e (AE g) -> get_weight e = Some N0.

Proof.
unfold AE. intros. eapply E_weights. eassumption.
Qed.

(* extremities of edges are in the graph *)
Lemma In_graph_edge_in_ext : forall e g,
In_graph_edge e g -> In_graph (fst_ext e) g /\ In_graph (snd_ext e) g.

Proof.
intros.
split. destruct H.
apply (proj1 (extremities_pmap g (fst_ext e))).

generalize (AE_weights _ _ H). intro Hw.
unfold AE in *.
rewrite (edge_eq e) in H.
simpl in Hw. rewrite Hw in H.
generalize (proj1 (edgemap_to_edgeset_charac _ _ _ _(sym_pmap g)) H). intro H0.
apply (proj2 (InterfFacts.in_find_iff _ _)).
unfold adj_set in H0.
case_eq (VertexMap.find (fst_ext e) (pmap g)); intros; rewrite H1 in H0.
intro Helim. inversion Helim.
elim (VertexSet.empty_1 H0).

apply (proj1 (extremities_imap g (fst_ext e))).
generalize (IE_weights _ _ H). intro Hw.
unfold IE in *.
rewrite (edge_eq e) in H.
simpl in Hw. rewrite Hw in H.
generalize (proj1 (edgemap_to_edgeset_charac _ _ _ _ (sym_imap g)) H). intro H0.
apply (proj2 (InterfFacts.in_find_iff _ _)).
unfold adj_set in H0.
case_eq (VertexMap.find (fst_ext e) (imap g)); intros; rewrite H1 in H0.
intro Helim. inversion Helim.
elim (VertexSet.empty_1 H0).

destruct H.
apply (proj1 (extremities_pmap g (snd_ext e))).
generalize (AE_weights _ _ H). intro Hw.
unfold AE in *.
rewrite (edge_eq e) in H. rewrite edge_comm in H.
simpl in Hw. rewrite Hw in H.
generalize (proj1 (edgemap_to_edgeset_charac _ _ _ _ (sym_pmap g)) H). intro H0.
apply (proj2 (InterfFacts.in_find_iff _ _)).
unfold adj_set in H0.
case_eq (VertexMap.find (snd_ext e) (pmap g)); intros; rewrite H1 in H0.
intro Helim. inversion Helim.
elim (VertexSet.empty_1 H0).

apply (proj1 (extremities_imap g (snd_ext e))).
generalize (IE_weights _ _ H). intro Hw.
unfold IE in *.
rewrite (edge_eq e) in H. rewrite edge_comm in H.
simpl in Hw. rewrite Hw in H.
generalize (proj1 (edgemap_to_edgeset_charac _ _ _ _ (sym_imap g)) H). intro H0.
apply (proj2 (InterfFacts.in_find_iff _ _)).
unfold adj_set in H0.
case_eq (VertexMap.find (snd_ext e) (imap g)); intros; rewrite H1 in H0.
intro Helim. inversion Helim.
elim (VertexSet.empty_1 H0).
Qed.

Lemma not_eq_extremities_map_merge : forall x y e m,
(forall a b, VertexSet.In a (adj_set b m) -> ~Vertex.eq a b) ->
VertexSet.In x (adj_set y (map_merge e m)) ->
~Vertex.eq x y.

Proof.
intros x y e m Hsimp H.
unfold map_merge in H.
set (f := (fun (y : VertexSet.elt) (m' : VertexMap.t VertexSet.t) =>
                   VertexMap.add y
                     (VertexSet.add (fst_ext e)
                        (VertexSet.remove (snd_ext e) (adj_set y m))) m')) in *.
set (s := (VertexSet.union
                  (VertexSet.remove (snd_ext e) (adj_set (fst_ext e) m))
                  (VertexSet.remove (fst_ext e) (adj_set (snd_ext e) m)))) in *.
set (s' := (VertexSet.remove (fst_ext e) (adj_set (snd_ext e) m))) in *.
intro.
unfold adj_set in H. rewrite MapFacts.remove_neq_o in H.
destruct (Vertex.eq_dec y (fst_ext e)).
rewrite MapFacts.add_eq_o in H.
unfold s in H.
destruct (VertexSet.union_1 H).
generalize (VertexSet.remove_3 H1). clear H1. intro H1.
rewrite H0 in H1. rewrite e0 in H1.
elim (Hsimp _ _ H1). auto.
unfold s' in H1.
rewrite H0 in H1. rewrite e0 in H1. elim (VertexSet.remove_1 (Vertex.eq_refl _) H1).
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H.

rewrite VertexSet.fold_1 in H.
set (f' := fun a e => f e a) in *.
induction (VertexSet.elements s'). simpl in H.
unfold adj_set in H.
fold (adj_set y m) in H.
elim (Hsimp _ _ H). assumption.

cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H1 y). clear H1. intro H1. simpl in H. inversion H1; clear H1.
unfold adj_set in H. rewrite <-H3 in H. elim (VertexSet.empty_1 H).

rewrite <-H2 in H.
set (tmp := fold_left f' l m) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec y a).
rewrite MapFacts.add_eq_o in H3.
inversion H3. subst. clear H3.
rewrite H4 in H. clear H4.
rewrite H0 in H.
destruct (proj1 (Props.Dec.F.add_iff _ _ _) H).
elim (n (Vertex.eq_sym H1)).
generalize (VertexSet.remove_3 H1). intro.
elim (Hsimp _ _ H3). auto. apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H3.
rewrite <-H3 in IHl.
apply IHl. rewrite <-H4. assumption.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H1. auto.
auto.

auto.

intro. rewrite MapFacts.remove_eq_o in H. elim (VertexSet.empty_1 H). auto.
Qed.

Lemma resolve_conflicts_map_0 : forall x y e g,
VertexSet.In x (adj_set y (resolve_conflicts (fst_ext e) (map_merge e (pmap g))
                                             (adj_set (fst_ext e) (map_merge e (pmap g)))
                                             (adj_set (fst_ext e) (imap_merge e g)))) ->
VertexSet.In x (adj_set y (map_merge e (pmap g))).

Proof.
intros.
unfold resolve_conflicts in H.
set (f :=  (fun (x : VertexSet.elt) (m : VertexMap.t VertexSet.t) =>
                VertexMap.add x (VertexSet.remove (fst_ext e) (adj_set x (map_merge e (pmap g)))) m)) in *.
set (s :=  (VertexSet.diff (adj_set (fst_ext e) (map_merge e (pmap g)))
               (adj_set (fst_ext e) (imap_merge e g)))) in *.
set (inter := (VertexSet.inter (adj_set (fst_ext e) (map_merge e (pmap g)))
                  (adj_set (fst_ext e) (imap_merge e g)))) in *.
unfold adj_set in H.
destruct (Vertex.eq_dec y (fst_ext e)). rewrite MapFacts.add_eq_o in H.
unfold s in H.
generalize (VertexSet.diff_1 H). intro H0.
unfold adj_set. rewrite (MapFacts.find_o _ e0). assumption.
apply Regs.eq_sym. auto.

rewrite MapFacts.add_neq_o in H.
rewrite VertexSet.fold_1 in H.
set (f' := fun a e => f e a) in *.
set (m := map_merge e (pmap g)) in *.
induction (VertexSet.elements inter). simpl in H. assumption.
cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H0 y). clear H0. simpl in H. intro H0. inversion H0; clear H0.
rewrite <-H2 in H. elim (VertexSet.empty_1 H).
set (tmp := fold_left f' l m) in *.
unfold f' in H2. unfold f in H2.
destruct (Vertex.eq_dec y a). rewrite MapFacts.add_eq_o in H2.
rewrite <-H1 in H. rewrite H3 in H. clear H3.
inversion H2; subst; clear H2.
unfold adj_set. rewrite (MapFacts.find_o _ e0).
apply (VertexSet.remove_3 H).
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H2.
apply IHl. rewrite <-H2. rewrite <-H1 in H. rewrite <-H3. assumption.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H0. auto.
auto.
auto.
Qed.

Lemma pmap_merge_sub : forall x y e g,
VertexSet.In x (adj_set y (pmap_merge e g (imap_merge e g))) ->
VertexSet.In x (adj_set y (map_merge e (pmap g))).

Proof.
exact (fun x y e g H => resolve_conflicts_map_0 _ _ _ _ H).
Qed.

Lemma pmap_merge_domain_1 : forall x e g,
In_graph_edge e g ->
VertexMap.In x (map_merge e (pmap g)) ->
VertexSet.In x (VertexSet.remove (snd_ext e) (V g)).

Proof.
intros x e g HH H.
unfold map_merge in H.
set (m := pmap g) in *.
set (s := VertexSet.remove (fst_ext e) (adj_set (snd_ext e) m)) in *.
set (adj := (VertexSet.union
           (VertexSet.remove (snd_ext e) (adj_set (fst_ext e) m)) s)) in *.
set (f := (fun (y : VertexSet.elt) (m'0 : VertexMap.t VertexSet.t) =>
            VertexMap.add y
              (VertexSet.add (fst_ext e)
                 (VertexSet.remove (snd_ext e) (adj_set y m))) m'0)) in *.
rewrite VertexSet.fold_1 in H.
set (f' := fun a e => f e a) in *.
rewrite MapFacts.in_find_iff in H.
assert (~Vertex.eq x (snd_ext e)).
intro. rewrite MapFacts.remove_eq_o in H. congruence. apply Regs.eq_sym. auto.
apply VertexSet.remove_2. auto.
rewrite MapFacts.remove_neq_o in H.
destruct (Vertex.eq_dec x (fst_ext e)).
rewrite e0. apply (proj1 (In_graph_edge_in_ext _ _ HH)).

cut (forall z, VertexSet.In z s -> VertexSet.In z (V g)). intro HHH.
generalize VertexSet.elements_2. intro H1.
generalize (H1 s x). clear H1. intro Helt.

induction (VertexSet.elements s). simpl in H. 
apply (proj1 (extremities_pmap g x)).
rewrite MapFacts.in_find_iff.
rewrite MapFacts.add_neq_o in H.
assumption.
auto.

cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H1 x). clear H1. intro H1. simpl in H. inversion H1.
rewrite MapFacts.add_neq_o in H.
rewrite <-H3 in H. congruence. auto.
set (tmp := fold_left f' l m) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec x a).
apply HHH. apply Helt. left. auto.
rewrite MapFacts.add_neq_o in H3.
apply IHl.
rewrite MapFacts.add_neq_o.
congruence.
auto.
intro. apply Helt. right. auto. auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f. intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set. 
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. unfold f'. unfold f. intros.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H1.
auto.
auto.

intros.
unfold s in H1.
generalize (VertexSet.remove_3 H1). clear H1. intro H1.
apply (proj1 (extremities_pmap g z)).
rewrite MapFacts.in_find_iff.
generalize (sym_pmap g _ _ H1). clear H1. intro H1.
unfold adj_set in H1.
destruct (VertexMap.find z (pmap g)).
congruence.
elim (VertexSet.empty_1 H1).
auto.
Qed.

Lemma pmap_merge_domain_2 : forall x e g,
In_graph_edge e g ->
VertexSet.In x (VertexSet.remove (snd_ext e) (V g)) ->
VertexMap.In x (map_merge e (pmap g)).

Proof.
intros x e g HH H.
unfold map_merge.
set (m := pmap g) in *.
set (s := VertexSet.remove (fst_ext e) (adj_set (snd_ext e) m)) in *.
set (adj := (VertexSet.union
           (VertexSet.remove (snd_ext e) (adj_set (fst_ext e) m)) s)) in *.
set (f := (fun (y : VertexSet.elt) (m'0 : VertexMap.t VertexSet.t) =>
            VertexMap.add y
              (VertexSet.add (fst_ext e)
                 (VertexSet.remove (snd_ext e) (adj_set y m))) m'0)) in *.
rewrite VertexSet.fold_1.
set (f' := fun a e => f e a) in *.
rewrite MapFacts.in_find_iff.
assert (~Vertex.eq x (snd_ext e)).
intro. elim (VertexSet.remove_1 (Vertex.eq_sym H0) H).
generalize (VertexSet.remove_3 H). clear H. intro H.
rewrite MapFacts.remove_neq_o.
destruct (Vertex.eq_dec x (fst_ext e)).
rewrite MapFacts.add_eq_o. congruence. apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.

induction (VertexSet.elements s). simpl.
rewrite <-MapFacts.in_find_iff.
apply (proj2 (extremities_pmap g x)). assumption.

cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H1 x). clear H1. intro H1. simpl. inversion H1.
set (tmp := fold_left f' l m) in *.
unfold f' in H4. unfold f in H4.
destruct (Vertex.eq_dec x a).
rewrite MapFacts.add_eq_o in H4. congruence. apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H4. congruence. auto.
congruence.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f. intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set. 
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. unfold f'. unfold f. intros.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H1.
auto.
auto.

auto.
auto.
Qed.

(* there is no loop in the graph *)
Lemma In_graph_edge_diff_ext : forall e g,
In_graph_edge e g -> ~Vertex.eq (snd_ext e) (fst_ext e).

Proof.
intros.
apply (not_eq_extremities g).
destruct H;[right|left].

generalize (AE_weights _ _ H). intro Hw.
unfold AE in *.
rewrite (edge_eq e) in H.
simpl in Hw. rewrite Hw in H.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ _(sym_pmap g)) H).

generalize (IE_weights _ _ H). intro Hw.
unfold IE in *.
rewrite (edge_eq e) in H.
simpl in Hw. rewrite Hw in H.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ _(sym_imap g)) H).
Qed.

Lemma extremities_in_merge_map e g :
In_graph_edge e g ->
(forall x,
VertexMap.In x (map_merge e (pmap g)) <->
VertexSet.In x (VertexSet.remove (snd_ext e) (V g))).

Proof.
intros e g HH x; split; intro H0.
generalize H0. intro H.
unfold map_merge in H0.
apply VertexSet.remove_2.
intro H1.
elim (VertexMap.remove_1 H1 H0).
generalize (proj1 (MapFacts.remove_in_iff _ _ _) H0). clear H0.
intro H0. destruct H0.
generalize (proj1 (MapFacts.add_in_iff _ _ _ _) H1). clear H1.
intro H1.
destruct H1.
rewrite <-H1.
apply (proj1 (In_graph_edge_in_ext _ _ HH)).
apply (proj1 (extremities_pmap g x)).
rewrite VertexSet.fold_1 in H1.
set (f := (fun (a : VertexMap.t VertexSet.t) (e0 : VertexSet.elt) =>
           VertexMap.add e0
             (VertexSet.add (fst_ext e)
                (VertexSet.remove (snd_ext e) (adj_set e0 (pmap g)))) a)) in *.
set (s := VertexSet.remove (fst_ext e) (adj_set (snd_ext e) (pmap g))) in *.
cut (forall z, In z (VertexSet.elements s) ->
                  VertexMap.In z (pmap g)).
intros HHH.
induction (VertexSet.elements s).
simpl in H1. assumption.
set (m := pmap g) in *.
cut (VertexMap.In x (f (fold_left f l m) a)).
clear H1. intro H1.
set (tmp := fold_left f l m) in *.
unfold f in H1.
destruct (Vertex.eq_dec x a).
rewrite e0. apply (HHH a). left. auto.
rewrite MapFacts.in_find_iff in H1.
rewrite MapFacts.add_neq_o in H1.
apply IHl.
rewrite MapFacts.in_find_iff.
assumption.
intros. apply HHH. right. assumption.
auto.

assert (EqualSetMap (fold_left f (a :: l) m) (f (fold_left f l m) a)).
apply fold_left_assoc_map.

unfold EqualSetMap. intros.
unfold f.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.add_m.
apply Regs.eq_refl.
apply RegFacts.Props.Dec.F.remove_m.
apply Regs.eq_refl.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ e1).
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.add_m.
apply Regs.eq_refl.
apply RegFacts.Props.Dec.F.remove_m.
apply Regs.eq_refl.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor. apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H2. auto.
auto.
rewrite MapFacts.in_find_iff.
generalize (H2 x). intro.
inversion H3.
rewrite MapFacts.in_find_iff in H1.
simpl in H1. rewrite <-H5 in H1. assumption.
congruence.

intros.
exists (adj_set z (pmap g)). apply VertexMap.elements_2.
apply VertexMap.elements_1.
unfold adj_set.
case_eq (VertexMap.find z (pmap g)); intros.
apply VertexMap.find_2. assumption.

assert (VertexSet.In z s).
apply VertexSet.elements_2.
apply In_InA. apply Regs.eq_refl. assumption.
unfold s in H4.
generalize (VertexSet.remove_3 H4). clear H4. intro H4.
generalize (sym_pmap g _ _ H4). clear H4. intro H4.
unfold adj_set in H4.
rewrite H3 in H4. elim (VertexSet.empty_1 H4).

unfold map_merge.
rewrite MapFacts.in_find_iff.
rewrite MapFacts.remove_neq_o.
destruct (Vertex.eq_dec x (fst_ext e)).
rewrite MapFacts.add_eq_o.
congruence.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite VertexSet.fold_1.
set (f := (fun (a : VertexMap.t VertexSet.t) (e0 : VertexSet.elt) =>
           VertexMap.add e0
             (VertexSet.add (fst_ext e)
                (VertexSet.remove (snd_ext e) (adj_set e0 (pmap g)))) a)) in *.
set (s := VertexSet.remove (fst_ext e) (adj_set (snd_ext e) (pmap g))) in *.
induction (VertexSet.elements s). simpl.
generalize (proj2 (extremities_pmap g x) (VertexSet.remove_3 H0)).
rewrite MapFacts.in_find_iff. auto.

set (m := pmap g) in *.
assert (EqualSetMap (fold_left f (a :: l) m) (f (fold_left f l m) a)).
apply fold_left_assoc_map.

unfold EqualSetMap. intros.
unfold f.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.add_m.
apply Regs.eq_sym. auto.
apply RegFacts.Props.Dec.F.remove_m.
apply Regs.eq_sym. auto.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ e1).
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.add_m.
apply Regs.eq_sym. auto.
apply RegFacts.Props.Dec.F.remove_m.
apply Regs.eq_refl.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor. apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H. auto.
auto.

generalize (H x). clear H. intro H.
inversion H.
simpl.
set (tmp := fold_left f l m) in *.
unfold f in H3.
destruct (Vertex.eq_dec x a).
rewrite MapFacts.add_eq_o in H3.
congruence.
intuition.
rewrite MapFacts.add_neq_o in H3.
rewrite H3 in IHl. congruence.
auto.
simpl. rewrite <-H1. congruence.
auto.
intro. elim (VertexSet.remove_1 H H0).
Qed.

Lemma extremities_in_merge_imap e g :
In_graph_edge e g ->
(forall x,
VertexMap.In x (imap_merge e g) <->
VertexSet.In x (VertexSet.remove (snd_ext e) (V g))).

Proof.
intros e g HH x; split; intro H0.
generalize H0. intro H.
unfold imap_merge in H0.
unfold map_merge in H0.
apply VertexSet.remove_2.
intro H1.
elim (VertexMap.remove_1 H1 H0).
generalize (proj1 (MapFacts.remove_in_iff _ _ _) H0). clear H0.
intro H0. destruct H0.
generalize (proj1 (MapFacts.add_in_iff _ _ _ _) H1). clear H1.
intro H1.
destruct H1.
rewrite <-H1.
apply (proj1 (In_graph_edge_in_ext _ _ HH)).
apply (proj1 (extremities_imap g x)).
rewrite VertexSet.fold_1 in H1.
set (f := (fun (a : VertexMap.t VertexSet.t) (e0 : VertexSet.elt) =>
           VertexMap.add e0
             (VertexSet.add (fst_ext e)
                (VertexSet.remove (snd_ext e) (adj_set e0 (imap g)))) a)) in *.
set (s := VertexSet.remove (fst_ext e) (adj_set (snd_ext e) (imap g))) in *.
cut (forall z, In z (VertexSet.elements s) ->
                  VertexMap.In z (imap g)).
intros HHH.
induction (VertexSet.elements s).
simpl in H1. assumption.
set (m := imap g) in *.
cut (VertexMap.In x (f (fold_left f l m) a)).
clear H1. intro H1.
set (tmp := fold_left f l m) in *.
unfold f in H1.
destruct (Vertex.eq_dec x a).
rewrite e0. apply (HHH a). left. auto.
rewrite MapFacts.in_find_iff in H1.
rewrite MapFacts.add_neq_o in H1.
apply IHl.
rewrite MapFacts.in_find_iff.
assumption.
intros. apply HHH. right. assumption.
auto.

assert (EqualSetMap (fold_left f (a :: l) m) (f (fold_left f l m) a)).
apply fold_left_assoc_map.

unfold EqualSetMap. intros.
unfold f.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.add_m.
intuition.
apply RegFacts.Props.Dec.F.remove_m.
intuition.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ e1).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.add_m.
intuition.
apply RegFacts.Props.Dec.F.remove_m.
intuition.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor. apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H2. auto.
auto.
rewrite MapFacts.in_find_iff.
generalize (H2 x). intro.
inversion H3.
rewrite MapFacts.in_find_iff in H1.
simpl in H1. rewrite <-H5 in H1. assumption.
congruence.

intros.
exists (adj_set z (imap g)). apply VertexMap.elements_2.
apply VertexMap.elements_1.
unfold adj_set.
case_eq (VertexMap.find z (imap g)); intros.
apply VertexMap.find_2. assumption.

assert (VertexSet.In z s).
apply VertexSet.elements_2.
apply In_InA. intuition. auto.
unfold s in H4.
generalize (VertexSet.remove_3 H4). clear H4. intro H4.
generalize (sym_imap g _ _ H4). clear H4. intro H4.
unfold adj_set in H4.
rewrite H3 in H4. elim (VertexSet.empty_1 H4).

unfold imap_merge.
unfold map_merge.
rewrite MapFacts.in_find_iff.
rewrite MapFacts.remove_neq_o.
destruct (Vertex.eq_dec x (fst_ext e)).
rewrite MapFacts.add_eq_o.
congruence.
intuition.
rewrite MapFacts.add_neq_o.
rewrite VertexSet.fold_1.
set (f := (fun (a : VertexMap.t VertexSet.t) (e0 : VertexSet.elt) =>
           VertexMap.add e0
             (VertexSet.add (fst_ext e)
                (VertexSet.remove (snd_ext e) (adj_set e0 (imap g)))) a)) in *.
set (s := VertexSet.remove (fst_ext e) (adj_set (snd_ext e) (imap g))) in *.
induction (VertexSet.elements s). simpl.
generalize (proj2 (extremities_imap g x) (VertexSet.remove_3 H0)).
rewrite MapFacts.in_find_iff. auto.

set (m := imap g) in *.
assert (EqualSetMap (fold_left f (a :: l) m) (f (fold_left f l m) a)).
apply fold_left_assoc_map.

unfold EqualSetMap. intros.
unfold f.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.add_m.
intuition.
apply RegFacts.Props.Dec.F.remove_m.
intuition.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ e1).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply RegFacts.Props.Dec.F.add_m.
intuition.
apply RegFacts.Props.Dec.F.remove_m.
intuition.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor. apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H. auto.
auto.

generalize (H x). clear H. intro H.
inversion H.
simpl.
set (tmp := fold_left f l m) in *.
unfold f in H3.
destruct (Vertex.eq_dec x a).
rewrite MapFacts.add_eq_o in H3.
congruence.
intuition.
rewrite MapFacts.add_neq_o in H3.
rewrite H3 in IHl. congruence.
intuition.
simpl. rewrite <-H1. congruence.
auto.
intro. elim (VertexSet.remove_1 H H0).
Qed.

Lemma sym_map_merge_map : forall e g m x y,
aff_edge e ->
In_graph_edge e g ->
(forall a b, VertexSet.In a (adj_set b m) ->
             VertexSet.In b (adj_set a m)) ->
(forall a b, VertexSet.In a (adj_set b (map_merge e m)) ->
             ~Vertex.eq a b) ->
~Vertex.eq x (snd_ext e) ->
~Vertex.eq y (snd_ext e) ->
VertexSet.In x (adj_set y (map_merge e m)) ->
VertexSet.In y (adj_set x (map_merge e m)).

Proof.
intros e g m x y Haff Hin Hsym Hnoteq Hsndx Hsndy H.
assert (~Vertex.eq x y) as Hdiff.
apply Hnoteq. assumption.
unfold map_merge in *.
set (f :=  (fun (y : VertexSet.elt) (m' : VertexMap.t VertexSet.t) =>
                   VertexMap.add y
                     (VertexSet.add (fst_ext e)
                        (VertexSet.remove (snd_ext e) (adj_set y m)))
                     m')) in *.
set (s := (VertexSet.union
                  (VertexSet.remove (snd_ext e)
                     (adj_set (fst_ext e) m))
                  (VertexSet.remove (fst_ext e)
                     (adj_set (snd_ext e) m)))) in *.
set (s' := adj_set (snd_ext e) m) in *.
cut (forall z, VertexSet.In z s' -> ~Vertex.eq z (fst_ext e) -> VertexSet.In z s). intro Himp.
unfold adj_set. rewrite MapFacts.remove_neq_o.
destruct (Vertex.eq_dec x (fst_ext e)).
rewrite MapFacts.add_eq_o.

unfold adj_set in H.
rewrite MapFacts.remove_neq_o in H.
destruct (Vertex.eq_dec y (fst_ext e)).
rewrite MapFacts.add_eq_o in H.
rewrite e1. rewrite <-e0. assumption.
intuition.

rewrite MapFacts.add_neq_o in H.
case_eq (VertexMap.find y (VertexSet.fold f (VertexSet.remove (fst_ext e) s') m)); intros.
rewrite H0 in H.

rewrite VertexSet.fold_1 in H0.
set (f' := fun a e => f e a) in *.

assert (eq_set_option (VertexMap.find (elt:=VertexSet.t) y
       (fold_left f' (VertexSet.elements (VertexSet.remove (fst_ext e) s'))
          m)) (Some t0)). rewrite H0. constructor. apply VertexSet.eq_refl.
generalize H1. clear H0 H1. intro H0.
generalize VertexSet.elements_2. intro.
generalize (H1 (VertexSet.remove (fst_ext e) s')). clear H1. intro HH.
induction (VertexSet.elements (VertexSet.remove (fst_ext e) s')).
unfold s. apply VertexSet.union_2.
apply VertexSet.remove_2.
auto.
apply Hsym. rewrite <-e0.
unfold adj_set. inversion H0. subst. rewrite H3. assumption.

cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H1 y). clear H1. intro H1. simpl in H0. inversion H1.
inversion H0. congruence.
set (tmp := fold_left f' l m) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec y a).
rewrite e1. 
apply Himp.
apply VertexSet.remove_3 with (x:= fst_ext e).
apply HH. left. intuition.
assert (VertexSet.In a (VertexSet.remove (fst_ext e) s')).
apply HH. left. intuition.
intro. elim (VertexSet.remove_1 (Vertex.eq_sym H6) H5).
rewrite MapFacts.add_neq_o in H3. clear H1.
apply IHl.
inversion H0. subst.
rewrite <-H1 in H2. clear H1. inversion H2. subst. clear H2.
rewrite <-H3. constructor.
rewrite <-H4. assumption.

intros. apply HH. right. assumption.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e2)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H1. auto. auto.

rewrite H0 in H.
elim (VertexSet.empty_1 H).
auto.
auto.
intuition.

rewrite MapFacts.add_neq_o.
unfold adj_set in H.
rewrite MapFacts.remove_neq_o in H.
destruct (Vertex.eq_dec y (fst_ext e)).
rewrite MapFacts.add_eq_o in H.

rewrite VertexSet.fold_1.
generalize VertexSet.elements_1. intro H0.
generalize (H0 (VertexSet.remove (fst_ext e) s') x). clear H0. intro H0.
induction (VertexSet.elements (VertexSet.remove (fst_ext e) s')). simpl.
unfold s in H.
destruct (VertexSet.union_1 H).
generalize (VertexSet.remove_3 H1). clear H1. intro H1.
generalize (Hsym _ _ H1). clear H1. intro H1.
rewrite <-e0 in H1. assumption.
generalize (VertexSet.remove_3 H1). clear H1. intro H1.
assert (VertexSet.In x (VertexSet.remove (fst_ext e) s')) by 
       (apply VertexSet.remove_2; auto).
generalize (H0 H2). intro H3. inversion H3.
set (f' := fun a e => f e a) in *.

cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H1 x). clear H1. intro H1. simpl. inversion H1.
set (tmp := fold_left f' l m) in *.
unfold f' in H4. unfold f in H4.
destruct (Vertex.eq_dec x a).
rewrite MapFacts.add_eq_o in H4. congruence.
intuition.
rewrite MapFacts.add_neq_o in H4. rewrite <-H4 in IHl.
apply IHl. intro.
generalize (H0 H2). clear H2. intro H2.
inversion H2; subst.
elim (n0 H6).
assumption.
auto.

set (tmp := fold_left f' l m) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec x a).
rewrite MapFacts.add_eq_o in H3.
inversion H3. subst. clear H3. clear H1.
rewrite H4. apply VertexSet.add_1. intuition. intuition.
rewrite MapFacts.add_neq_o in H3. rewrite <-H3 in IHl.
rewrite H4. apply IHl. intro.
generalize (H0 H5). clear H5. intro H5.
inversion H5; subst.
elim (n0 H7).
assumption.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e2)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H1. auto. auto.

intuition.

rewrite MapFacts.add_neq_o in H.
rewrite VertexSet.fold_1 in H. rewrite VertexSet.fold_1.
set (f' := fun a e => f e a) in *.
induction (VertexSet.elements (VertexSet.remove (fst_ext e) s')). simpl in H. simpl.
apply (Hsym _ _ H).

cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H0 x). generalize (H0 y). clear H0. intros H0 HH0. simpl. simpl in H. inversion H0.
rewrite <-H2 in H. elim (VertexSet.empty_1 H).
set (tmp := fold_left f' l m) in *.
unfold f' in H2. unfold f in H2.
destruct (Vertex.eq_dec y a).
rewrite MapFacts.add_eq_o in H2.
inversion HH0.
unfold f' in H6. unfold f in H6.
destruct (Vertex.eq_dec x a).
elim Hdiff. apply (Vertex.eq_trans e1 (Vertex.eq_sym e0)).
rewrite MapFacts.add_neq_o in H6.

cut (VertexMap.In x tmp).
intro H7. rewrite MapFacts.in_find_iff in H7. congruence.
cut (VertexMap.In x m -> VertexMap.In x tmp).
intro H7. apply H7. clear H7.
rewrite MapFacts.in_find_iff. intro.

rewrite <-H1 in *. rewrite H3 in H. clear H0 HH0 H1 H5 H6 IHl.
inversion H2. subst. clear H2. clear H3.
destruct (proj1 (Props.Dec.F.add_iff _ _ _) H). elim n. auto.
generalize (VertexSet.remove_3 H0). clear H H0. intro H.
generalize (Hsym _ _ H). clear H. intro H.
unfold adj_set in H. rewrite H4 in H. elim (VertexSet.empty_1 H).

clear IHl H H0 HH0 H1 H2 H3 H5 H6. intro.
unfold tmp.
induction l. simpl. assumption.

cut (EqualSetMap (fold_left f' (a0 :: l) m) (f' (fold_left f' l m) a0)). intro.
generalize (H0 x). clear H0. simpl. intro H0. inversion H0.
set (tmp' := fold_left f' l m) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec x a0).
rewrite MapFacts.add_eq_o in H3. congruence. intuition.
rewrite MapFacts.add_neq_o in H3.
rewrite MapFacts.in_find_iff in IHl. congruence. intuition.
rewrite MapFacts.in_find_iff. congruence.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e2)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s1); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a1).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H0. auto. auto.

auto.
clear H0 HH0.
rewrite <-H1 in H.
unfold f' in H5. unfold f in H5.
destruct (Vertex.eq_dec x a).
elim Hdiff. apply Vertex.eq_trans with (y:=a); auto.
rewrite MapFacts.add_neq_o in H5.
rewrite <-H5 in *.
inversion H2. subst. clear H2.
rewrite H3 in H.
destruct (proj1 (Props.Dec.F.add_iff _ _ _) H). elim n. auto.
generalize (VertexSet.remove_3 H0). clear H H0. intro H.

case_eq (VertexMap.find y tmp); intros.
rewrite H0 in IHl.
rewrite H6. apply IHl.

clear IHl H1 H6 H4 H3 H5.
unfold tmp in H0.
unfold adj_set in H. rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)) in H.
assert (eq_set_option (VertexMap.find y (fold_left f' l m)) (Some t0)).
rewrite H0. constructor. apply VertexSet.eq_refl.
generalize H1. clear H0 H1. intro H0.
induction l. simpl in H0. inversion H0. subst. clear H0. rewrite <-H1 in H. rewrite <-H3. assumption.
cut (EqualSetMap (fold_left f' (a0 :: l) m) (f' (fold_left f' l m) a0)). intro.
generalize (H1 y). clear H1. simpl in H0. intro H1. inversion H1. clear H1.
set (tmp' := fold_left f' l m) in *.
unfold f' in H4. unfold f in H4.
destruct (Vertex.eq_dec y a0).
rewrite MapFacts.add_eq_o in H4. congruence. intuition.
rewrite MapFacts.add_neq_o in H4.

case_eq (VertexMap.find y m); intros.
clear H.

assert (VertexMap.In y tmp').
clear H3 H4 IHl H0.
unfold tmp'. induction l. simpl.
rewrite MapFacts.in_find_iff. congruence.

cut (EqualSetMap (fold_left f' (a1 :: l) m) (f' (fold_left f' l m) a1)). intro.
generalize (H y). clear H. intro H. simpl. inversion H. clear H.
set (tmp'' := fold_left f' l m) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec y a1).
rewrite MapFacts.add_eq_o in H3. congruence. intuition.
rewrite MapFacts.add_neq_o in H3.
rewrite MapFacts.in_find_iff in IHl. rewrite <-H3 in IHl. congruence.
auto.
rewrite MapFacts.in_find_iff. rewrite <-H0. congruence.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e2)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s2); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a2).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H. auto. auto.

rewrite MapFacts.in_find_iff in H. congruence.
rewrite H1 in H. elim (VertexSet.empty_1 H).
auto. 

rewrite <-H2 in *. inversion H0. subst. clear H0 H1.

set (tmp' := fold_left f' l m) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec y a0). rewrite MapFacts.add_eq_o in H3.
inversion H3. subst. clear H3.
case_eq (VertexMap.find y m); intros.
rewrite H0 in H.
rewrite <-H7. rewrite H4. 
apply VertexSet.add_2.
apply VertexSet.remove_2.
auto.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
rewrite H0. assumption.
rewrite H0 in H. elim (VertexSet.empty_1 H).
intuition.
rewrite MapFacts.add_neq_o in H3.

apply IHl.
rewrite <-H3. constructor.
rewrite <-H4. rewrite <-H7. apply VertexSet.eq_refl.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e2)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s2); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a1).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H1. auto. auto.

unfold adj_set in H. rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)) in H.
clear IHl H1 H6 H4 H5 H3.
unfold tmp in H0.
induction l. simpl in H0.
rewrite H0 in H. elim (VertexSet.empty_1 H).

cut (EqualSetMap (fold_left f' (a0 :: l) m) (f' (fold_left f' l m) a0)). intro.
generalize (H1 y). clear H1. intro H1. simpl in H0. inversion H1.
set (tmp' := fold_left f' l m) in *.
unfold f' in H4. unfold f in H4.
destruct (Vertex.eq_dec y a0).
rewrite MapFacts.add_eq_o in H4. congruence. intuition.
rewrite MapFacts.add_neq_o in H4.
apply IHl. auto. auto.

congruence.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e2)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s2); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a1).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H1. auto. auto.

auto.
intuition.
rewrite MapFacts.add_neq_o in H2.
rewrite <-H2 in *. rewrite <-H1 in *.

inversion HH0.
unfold f' in H6. unfold f in H6.
destruct (Vertex.eq_dec x a).
rewrite MapFacts.add_eq_o in H6. congruence. intuition.
rewrite MapFacts.add_neq_o in H6.
rewrite <-H6 in IHl.
apply IHl. rewrite <-H3. assumption.
auto.

unfold f' in H5. unfold f in H5.
destruct (Vertex.eq_dec x a).
rewrite MapFacts.add_eq_o in H5.
clear H0 HH0.

inversion H5. subst. clear H5.
rewrite H6.
apply VertexSet.add_2.
apply VertexSet.remove_2.
auto.
apply Hsym.
rewrite <-e0.
rewrite H3 in H. clear IHl H1 H4 H6.
unfold tmp in H2.
assert (eq_set_option (Some s'0) (VertexMap.find y (fold_left f' l m))).
rewrite <-H2. constructor. apply VertexSet.eq_refl.
generalize H0. clear H0 H2. intro H2.
induction l. simpl in H2.
unfold adj_set. inversion H2. subst. rewrite <-H4. assumption.

cut (EqualSetMap (fold_left f' (a0 :: l) m) (f' (fold_left f' l m) a0)). intro.
generalize (H0 y). clear H0. simpl in H2. intro H0. inversion H0. clear H0.
rewrite <-H4 in H2. inversion H2.
set (tmp' := fold_left f' l m) in *.
unfold f' in H4. unfold f in H4.
destruct (Vertex.eq_dec y a0).
rewrite MapFacts.add_eq_o in H4. inversion H4. subst. clear H4.
inversion H2. subst. rewrite <-H6 in H1. inversion H1. subst.
apply VertexSet.remove_3 with (x:=snd_ext e).
apply VertexSet.add_3 with (x:= fst_ext e).
auto.
unfold adj_set. rewrite (MapFacts.find_o _ e1). rewrite <-H5. rewrite <-H7. assumption.
intuition.
rewrite MapFacts.add_neq_o in H4.
apply IHl.
rewrite <-H4. constructor. rewrite <-H1 in H2. inversion H2. subst.
rewrite H8. assumption.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e2)).
apply VertexSet.eq_refl. intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s2); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a1).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H0. auto. auto.
intuition.
rewrite MapFacts.add_neq_o in H5.
rewrite <-H5 in *.
rewrite H6. apply IHl.
rewrite <-H3. assumption.
auto.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H0. auto. auto.

auto.
auto.
auto.
auto.

clear H.
unfold s. unfold s'. intros z H Hne.
apply VertexSet.union_3. apply VertexSet.remove_2; auto.
Qed.

Lemma not_eq_extremities_merge_map : forall e g,
aff_edge e ->
forall x y,
VertexSet.In x (adj_set y (imap_merge e g)) \/
VertexSet.In x (adj_set y (pmap_merge e g (imap_merge e g))) ->
~Vertex.eq x y.

Proof.
intros. destruct H0.
apply (not_eq_extremities_map_merge x y e (imap g)). 
intros. apply (not_eq_extremities g). left. assumption. assumption.
apply (not_eq_extremities_map_merge x y e (pmap g)).
intros. apply (not_eq_extremities g). right. assumption.
apply pmap_merge_sub. assumption.
Qed.

Lemma sym_merge : forall e g,
aff_edge e ->
In_graph_edge e g ->
forall x y,
VertexSet.In x (adj_set y (map_merge e (pmap g))) ->
VertexSet.In y (adj_set x (map_merge e (pmap g))).

Proof.
intros e g Haff Hin x y H.
apply sym_map_merge_map with (g:=g); auto.
apply (sym_pmap g).
intros. apply (not_eq_extremities_map_merge _ _ e (pmap g)).
intros. apply (not_eq_extremities g). right. auto.
assumption.

assert (~Vertex.eq y (snd_ext e)) as Hy.
intro.
generalize (extremities_in_merge_map e g Hin y).
rewrite MapFacts.in_find_iff. intro.
unfold adj_set in H.
case_eq (VertexMap.find y (map_merge e (pmap g))); intros.
rewrite H2 in H1.
assert (VertexSet.In y (VertexSet.remove (snd_ext e) (V g))).
rewrite <-H1. congruence.
elim (VertexSet.remove_1 (Vertex.eq_sym H0) H3).
rewrite H2 in H. elim (VertexSet.empty_1 H).

intro.
unfold map_merge in H.

set (f :=  (fun (y : VertexSet.elt) (m' : VertexMap.t VertexSet.t) =>
                   VertexMap.add y
                     (VertexSet.add (fst_ext e)
                        (VertexSet.remove (snd_ext e) (adj_set y (pmap g))))
                     m')) in *.
set (s := (VertexSet.union
                  (VertexSet.remove (snd_ext e)
                     (adj_set (fst_ext e) (pmap g)))
                  (VertexSet.remove (fst_ext e)
                     (adj_set (snd_ext e) (pmap g))))) in *.
set (s' := adj_set (snd_ext e) (pmap g)) in *.

unfold adj_set in H.
rewrite MapFacts.remove_neq_o in H.
destruct (Vertex.eq_dec y (fst_ext e)).
rewrite MapFacts.add_eq_o in H.
unfold s in H.
destruct (VertexSet.union_1 H).
elim (VertexSet.remove_1 (Vertex.eq_sym H0) H1).
generalize (VertexSet.remove_3 H1). clear H1. intro H1.
unfold s' in H1.

elim (not_eq_extremities g x (snd_ext e)).
right. assumption.
assumption.
intuition.
rewrite MapFacts.add_neq_o in H.

rewrite VertexSet.fold_1 in H.
set (f' := fun a e => f e a) in *.
generalize VertexSet.elements_1. intro.
generalize (H1 (VertexSet.remove (fst_ext e) s') y). clear H1. intro H1.
induction (VertexSet.elements (VertexSet.remove (fst_ext e) s')).
simpl in H.
unfold s' in H1.
assert (InA Vertex.eq y nil).
apply H1.
apply VertexSet.remove_2. auto.
apply (sym_pmap g). rewrite <-H0. assumption. inversion H2.

cut (EqualSetMap (fold_left f' (a :: l) (pmap g)) (f' (fold_left f' l (pmap g)) a)). intro.
generalize (H2 y). clear H2. intro H2. simpl in H. inversion H2; clear H2.
rewrite <-H4 in *.
elim (VertexSet.empty_1 H).
set (tmp := fold_left f' l (pmap g)) in *.
unfold f' in H4. unfold f in H4.
destruct (Vertex.eq_dec y a).
rewrite MapFacts.add_eq_o in H4.
rewrite <-H3 in *. clear H3. inversion H4. subst. clear H4.
rewrite H5 in H. clear H5.
destruct (proj1 (Props.Dec.F.add_iff _ _ _) H).
elim (In_graph_edge_diff_ext _ _ Hin).
apply Vertex.eq_trans with (y := x); auto.
elim (VertexSet.remove_1 (Vertex.eq_sym H0) H2).
intuition.
rewrite MapFacts.add_neq_o in H4. rewrite <-H4 in IHl.
apply IHl.
rewrite <-H5. rewrite <-H3 in H. assumption.
intro. generalize (H1 H2). clear H2. intro H2.
inversion H2; subst.
elim (n0 H7).
assumption.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H2. auto. auto.

auto.
auto.

intro.
generalize (extremities_in_merge_map e g Hin y).
rewrite MapFacts.in_find_iff. intro.
unfold adj_set in H.
case_eq (VertexMap.find y (map_merge e (pmap g))); intros.
rewrite H2 in H1.
assert (VertexSet.In y (VertexSet.remove (snd_ext e) (V g))).
rewrite <-H1. congruence.
elim (VertexSet.remove_1 (Vertex.eq_sym H0) H3).
rewrite H2 in H. elim (VertexSet.empty_1 H).
Qed.

Lemma sym_imap_merge_map : forall e g,
aff_edge e ->
In_graph_edge e g ->
forall x y,
VertexSet.In x (adj_set y (imap_merge e g)) ->
VertexSet.In y (adj_set x (imap_merge e g)).

Proof.
intros e g Haff Hin x y H.
apply sym_map_merge_map with (g:=g); auto.
apply (sym_imap g).
intros. apply (not_eq_extremities_merge_map e g Haff). left. assumption.

assert (~Vertex.eq y (snd_ext e)) as Hy.
intro.
generalize (extremities_in_merge_imap e g Hin y).
rewrite MapFacts.in_find_iff. intro.
unfold adj_set in H.
case_eq (VertexMap.find y (imap_merge e g)); intros.
rewrite H2 in H1.
assert (VertexSet.In y (VertexSet.remove (snd_ext e) (V g))).
rewrite <-H1. congruence.
elim (VertexSet.remove_1 (Vertex.eq_sym H0) H3).
rewrite H2 in H. elim (VertexSet.empty_1 H).

intro.
unfold imap_merge in H.
unfold map_merge in H.

set (f :=  (fun (y : VertexSet.elt) (m' : VertexMap.t VertexSet.t) =>
                   VertexMap.add y
                     (VertexSet.add (fst_ext e)
                        (VertexSet.remove (snd_ext e) (adj_set y (imap g))))
                     m')) in *.
set (s := (VertexSet.union
                  (VertexSet.remove (snd_ext e)
                     (adj_set (fst_ext e) (imap g)))
                  (VertexSet.remove (fst_ext e)
                     (adj_set (snd_ext e) (imap g))))) in *.
set (s' := adj_set (snd_ext e) (imap g)) in *.

unfold adj_set in H.
rewrite MapFacts.remove_neq_o in H.
destruct (Vertex.eq_dec y (fst_ext e)).
rewrite MapFacts.add_eq_o in H.
unfold s in H.
destruct (VertexSet.union_1 H).
elim (VertexSet.remove_1 (Vertex.eq_sym H0) H1).
generalize (VertexSet.remove_3 H1). clear H1. intro H1.
unfold s' in H1.

elim (not_eq_extremities g x (snd_ext e)).
left. assumption.
assumption.
intuition.
rewrite MapFacts.add_neq_o in H.

rewrite VertexSet.fold_1 in H.
set (f' := fun a e => f e a) in *.
generalize VertexSet.elements_1. intro.
generalize (H1 (VertexSet.remove (fst_ext e) s') y). clear H1. intro H1.
induction (VertexSet.elements (VertexSet.remove (fst_ext e) s')).
simpl in H.
unfold s' in H1.
assert (InA Vertex.eq y nil).
apply H1.
apply VertexSet.remove_2. auto.
apply (sym_imap g). rewrite <-H0. assumption. inversion H2.

cut (EqualSetMap (fold_left f' (a :: l) (imap g)) (f' (fold_left f' l (imap g)) a)). intro.
generalize (H2 y). clear H2. intro H2. simpl in H. inversion H2; clear H2.
rewrite <-H4 in *.
elim (VertexSet.empty_1 H).
set (tmp := fold_left f' l (imap g)) in *.
unfold f' in H4. unfold f in H4.
destruct (Vertex.eq_dec y a).
rewrite MapFacts.add_eq_o in H4.
rewrite <-H3 in *. clear H3. inversion H4. subst. clear H4.
rewrite H5 in H. clear H5.
destruct (proj1 (Props.Dec.F.add_iff _ _ _) H).
elim (In_graph_edge_diff_ext _ _ Hin).
apply Vertex.eq_trans with (y := x); auto.
elim (VertexSet.remove_1 (Vertex.eq_sym H0) H2).
intuition.
rewrite MapFacts.add_neq_o in H4. rewrite <-H4 in IHl.
apply IHl.
rewrite <-H5. rewrite <-H3 in H. assumption.
intro. generalize (H1 H2). clear H2. intro H2.
inversion H2; subst.
elim (n0 H7).
assumption.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H2. auto. auto.

auto.
auto.

intro.
generalize (extremities_in_merge_imap e g Hin y).
rewrite MapFacts.in_find_iff. intro.
unfold adj_set in H.
case_eq (VertexMap.find y (imap_merge e g)); intros.
rewrite H2 in H1.
assert (VertexSet.In y (VertexSet.remove (snd_ext e) (V g))).
rewrite <-H1. congruence.
elim (VertexSet.remove_1 (Vertex.eq_sym H0) H3).
rewrite H2 in H. elim (VertexSet.empty_1 H).
Qed.

Lemma pmap_merge_in_merge : forall x e g,
aff_edge e ->
In_graph_edge e g ->
VertexMap.In x (pmap_merge e g (imap_merge e g)) ->
VertexMap.In x (map_merge e (pmap g)).

Proof.
intros x e g Haff HH H.
unfold pmap_merge in H.
unfold resolve_conflicts in H.
set (f := (fun (x : VertexSet.elt) (m : VertexMap.t VertexSet.t) =>
             VertexMap.add x
               (VertexSet.remove (fst_ext e)
                  (adj_set x (map_merge e (pmap g)))) m)) in *.
rewrite MapFacts.in_find_iff in *. intro H0.
destruct (Vertex.eq_dec x (fst_ext e)).
rewrite (MapFacts.find_o _ e0) in H0.
assert (VertexMap.In (fst_ext e) (map_merge e (pmap g))).
apply pmap_merge_domain_2. assumption.
apply VertexSet.remove_2. apply (In_graph_edge_diff_ext _ _ HH).
apply (proj1 (In_graph_edge_in_ext _ _ HH)).
rewrite MapFacts.in_find_iff in H1. congruence.
rewrite MapFacts.add_neq_o in H.
set (s' :=  (VertexSet.inter (adj_set (fst_ext e) (map_merge e (pmap g)))
            (adj_set (fst_ext e) (imap_merge e g)))) in *.
set (m := map_merge e (pmap g)) in *.
rewrite VertexSet.fold_1 in H.
set (f' := fun a e => f e a) in *.
assert (forall z, InA Vertex.eq z (VertexSet.elements s') ->
                  VertexMap.In z m) as Hin.
intros.
apply pmap_merge_domain_2. assumption.
generalize (VertexSet.elements_2 H1). clear H1. intro H1.
unfold s' in H1. generalize (VertexSet.inter_1 H1).
generalize (VertexSet.inter_2 H1). clear H1. intros.
rewrite <-(extremities_in_merge_imap e g HH).
generalize (sym_imap_merge_map e g Haff HH _ _ H1). intro.
rewrite MapFacts.in_find_iff. intro.
unfold adj_set in H3. rewrite H4 in H3. elim (VertexSet.empty_1 H3).
induction (VertexSet.elements s'). simpl in H. congruence.
cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H1 x). clear H1. simpl in H. intro H1. inversion H1; clear H1.
congruence.
set (tmp := fold_left f' l m) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec x a).
rewrite MapFacts.add_eq_o in H3. inversion H3; subst; clear H3.
rewrite <-H2 in H.
rewrite (MapFacts.find_o _ e0) in H0.
assert (VertexMap.In a m).
apply Hin. left. auto.
rewrite MapFacts.in_find_iff in H1. congruence.
intuition.
rewrite MapFacts.add_neq_o in H3.
apply IHl. congruence.
intros. apply Hin. right. auto.
auto.


apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H1. auto. auto.
auto.
Qed.

Lemma pmap_merge_merge_in : forall x e g,
In_graph_edge e g ->
VertexMap.In x (map_merge e (pmap g)) ->
VertexMap.In x (pmap_merge e g (imap_merge e g)).

Proof.
intros x e g HH H.
unfold pmap_merge.
unfold resolve_conflicts.
set (f :=  (fun (x0 : VertexSet.elt) (m : VertexMap.t VertexSet.t) =>
         VertexMap.add x0
           (VertexSet.remove (fst_ext e) (adj_set x0 (map_merge e (pmap g))))
           m)) in *.
set (s :=  (VertexSet.inter (adj_set (fst_ext e) (map_merge e (pmap g)))
           (adj_set (fst_ext e) (imap_merge e g)))) in *.
rewrite MapFacts.in_find_iff.
destruct (Vertex.eq_dec x (fst_ext e)).
rewrite MapFacts.add_eq_o. congruence.
intuition.
rewrite MapFacts.add_neq_o.
intro H0.
rewrite VertexSet.fold_1 in H0.
set (f' := fun a e => f e a) in *.
assert (VertexMap.find x (map_merge e (pmap g)) = None).
induction (VertexSet.elements s). simpl in H0. assumption.
set (m := map_merge e (pmap g)) in *.
cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H1 x). clear H1. intro H1. simpl in H0. inversion H1; clear H1.
set (tmp := fold_left f' l m) in *.
unfold f' in H4. unfold f in H4.
destruct (Vertex.eq_dec x a). rewrite MapFacts.add_eq_o in H4. congruence.
intuition.
rewrite MapFacts.add_neq_o in H4.
apply IHl. auto.
auto.

congruence.
apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H1. auto. auto.
auto.

rewrite MapFacts.in_find_iff in H. congruence.
auto.
Qed.

Lemma extremities_in_merge_pmap e g :
aff_edge e ->
In_graph_edge e g ->
(forall x,
VertexMap.In x (pmap_merge e g (imap_merge e g)) <->
VertexSet.In x (VertexSet.remove (snd_ext e) (V g))).

Proof.
intros e g Haff HH x;split; intro H0.
apply pmap_merge_domain_1. assumption. 
apply pmap_merge_in_merge. assumption.
assumption. assumption.
apply pmap_merge_merge_in. assumption.
apply pmap_merge_domain_2. assumption.
assumption.
Qed.

Lemma merge_conflicts_aux_1 : forall e g,
aff_edge e ->
In_graph_edge e g ->
forall x y,
VertexSet.In x (adj_set y (imap_merge e g)) ->
~Vertex.eq y (fst_ext e) ->
~Vertex.eq x (fst_ext e) ->
VertexSet.In x (adj_set y (imap g)).

Proof.
intros.
unfold imap_merge in H1.
unfold map_merge in H1.
set (m := imap g) in *.
set (f := fun (y : VertexSet.elt) (m' : VertexMap.t VertexSet.t) =>
               VertexMap.add y
              (VertexSet.add (fst_ext e)
              (VertexSet.remove (snd_ext e) (adj_set y m)))
              m') in *.
set (s :=  (VertexSet.union
                   (VertexSet.remove (snd_ext e)
                      (adj_set (fst_ext e) m))
                   (VertexSet.remove (fst_ext e)
                      (adj_set (snd_ext e) m)))) in *.
set (s' := (adj_set (snd_ext e) m)) in *.
unfold adj_set in H1.
destruct (Vertex.eq_dec y (snd_ext e)). 
rewrite MapFacts.remove_eq_o in H1. elim (VertexSet.empty_1 H1).
intuition.
rewrite MapFacts.remove_neq_o in H1. rewrite MapFacts.add_neq_o in H1.
rewrite VertexSet.fold_1 in H1. set (f' := fun a e => f e a) in *.
induction (VertexSet.elements (VertexSet.remove (fst_ext e) s')). simpl in H1.
assumption.
cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H4 y). clear H4. intro H4. simpl in H1. inversion H4; subst; clear H4.
rewrite <-H6 in H1. elim (VertexSet.empty_1 H1).
set (tmp := fold_left f' l m) in *.
unfold f' in H6. unfold f in H6.
destruct (Vertex.eq_dec y a). rewrite MapFacts.add_eq_o in H6.
rewrite <-H5 in H1. rewrite H7 in H1.
inversion H6; subst; clear H6.
destruct (proj1 (Props.Dec.F.add_iff _ _ _) H1). elim H3; auto.
generalize (VertexSet.remove_3 H4). intro.
unfold adj_set. rewrite (MapFacts.find_o _ e0). assumption.
intuition.
rewrite MapFacts.add_neq_o in H6.
rewrite <-H6 in IHl.
apply IHl. rewrite <-H7. rewrite <-H5 in H1. assumption.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H4. auto. auto.

auto.
auto.
Qed.

Lemma merge_conflicts_aux_2 : forall e g,
aff_edge e ->
In_graph_edge e g ->
forall x y,
VertexSet.In x (adj_set y (map_merge e (pmap g))) ->
~Vertex.eq y (fst_ext e) ->
~Vertex.eq x (fst_ext e) ->
VertexSet.In x (adj_set y (pmap g)).

Proof.
intros.
unfold map_merge in H1.
set (m := pmap g) in *.
set (f := fun (y : VertexSet.elt) (m' : VertexMap.t VertexSet.t) =>
               VertexMap.add y
              (VertexSet.add (fst_ext e)
              (VertexSet.remove (snd_ext e) (adj_set y m)))
              m') in *.
set (s :=  (VertexSet.union
                   (VertexSet.remove (snd_ext e)
                      (adj_set (fst_ext e) m))
                   (VertexSet.remove (fst_ext e)
                      (adj_set (snd_ext e) m)))) in *.
set (s' := (adj_set (snd_ext e) m)) in *.
unfold adj_set in H1.
destruct (Vertex.eq_dec y (snd_ext e)). 
rewrite MapFacts.remove_eq_o in H1. elim (VertexSet.empty_1 H1).
intuition.
rewrite MapFacts.remove_neq_o in H1. rewrite MapFacts.add_neq_o in H1.
rewrite VertexSet.fold_1 in H1. set (f' := fun a e => f e a) in *.
induction (VertexSet.elements (VertexSet.remove (fst_ext e) s')). simpl in H1.
assumption.
cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H4 y). clear H4. intro H4. simpl in H1. inversion H4; subst; clear H4.
rewrite <-H6 in H1. elim (VertexSet.empty_1 H1).
set (tmp := fold_left f' l m) in *.
unfold f' in H6. unfold f in H6.
destruct (Vertex.eq_dec y a). rewrite MapFacts.add_eq_o in H6.
rewrite <-H5 in H1. rewrite H7 in H1.
inversion H6; subst; clear H6.
destruct (proj1 (Props.Dec.F.add_iff _ _ _) H1). elim H3; auto.
generalize (VertexSet.remove_3 H4). intro.
unfold adj_set. rewrite (MapFacts.find_o _ e0). assumption.
intuition.
rewrite MapFacts.add_neq_o in H6.
rewrite <-H6 in IHl.
apply IHl. rewrite <-H7. rewrite <-H5 in H1. assumption.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H4. auto. auto.

auto.
auto.
Qed.

Lemma merge_conflicts : forall e g,
aff_edge e ->
In_graph_edge e g ->
forall x y,
VertexSet.In x (adj_set y (imap_merge e g)) ->
VertexSet.In x (adj_set y (map_merge e (pmap g))) ->
~Vertex.eq y (fst_ext e) ->
~Vertex.eq x (fst_ext e) ->
False.

Proof.
intros.
apply (simple_graph g x y).
split.
apply (merge_conflicts_aux_1 e g H H0 x y H1 H3 H4).
apply (merge_conflicts_aux_2 e g H H0 x y H2 H3 H4).
Qed.

Lemma resolve_conflicts_map_3 : forall x y e g,
aff_edge e ->
In_graph_edge e g ->
VertexSet.In x (adj_set y (imap_merge e g)) /\
VertexSet.In x (adj_set y (resolve_conflicts (fst_ext e) (map_merge e (pmap g))
                                                         (adj_set (fst_ext e) (map_merge e (pmap g)))
                                                         (adj_set (fst_ext e) (imap_merge e g))))

-> False.

Proof.
intros x y e g Haff Hin H. destruct H.
unfold resolve_conflicts in H0.
set (f :=  (fun (x : VertexSet.elt) (m : VertexMap.t VertexSet.t) =>
                 VertexMap.add x
                   (VertexSet.remove (fst_ext e)
                      (adj_set x (map_merge e (pmap g)))) m)) in *.
set (s := (VertexSet.diff (adj_set (fst_ext e) (map_merge e (pmap g)))
                (adj_set (fst_ext e) (imap_merge e g)))) in *.
set (s' := (VertexSet.inter (adj_set (fst_ext e) (map_merge e (pmap g)))
                   (adj_set (fst_ext e) (imap_merge e g)))) in *.
rewrite VertexSet.fold_1 in H0.
set (f' := fun a e => f e a) in *.
generalize VertexSet.elements_1. intro HH.
generalize (HH s' y). clear HH. intro HH.
induction (VertexSet.elements s'). simpl in H0.
destruct (Vertex.eq_dec y (fst_ext e)).
unfold adj_set in H0. rewrite MapFacts.add_eq_o in H0.
elim (VertexSet.diff_2 H0).
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)). assumption.
intuition.
unfold adj_set in H0. rewrite MapFacts.add_neq_o in H0.

assert (InA Vertex.eq y nil).
apply HH.
unfold s'. apply VertexSet.inter_3.
cut (Vertex.eq x (fst_ext e)). intro.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym H1)).
apply sym_merge; auto.
destruct (Vertex.eq_dec x (fst_ext e)).
intuition.
apply False_ind. apply (merge_conflicts e g Haff Hin x y); auto.

destruct (Vertex.eq_dec x (fst_ext e)).
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
apply (sym_imap_merge_map e g Haff Hin). assumption.
apply False_ind.
apply (merge_conflicts e g Haff Hin x y); auto. inversion H1.
auto.

set (m := map_merge e (pmap g)) in *.
cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H1 y). clear H1. simpl in H0. intro H1. inversion H1; clear H1.
set (tmp := fold_left f' l m) in *.
unfold f' in H4. unfold f in H4.
destruct (Vertex.eq_dec y a). rewrite MapFacts.add_eq_o in H4. congruence.
intuition.
rewrite MapFacts.add_neq_o in H4.
destruct (Vertex.eq_dec y (fst_ext e)).
unfold adj_set in H0. rewrite MapFacts.add_eq_o in H0.
unfold adj_set in IHl. rewrite MapFacts.add_eq_o in IHl.
apply IHl. assumption. intros.
generalize (HH H1). intro H2. inversion H2; subst.
elim (n H6). auto.
intuition.
intuition.

unfold adj_set in H0. rewrite MapFacts.add_neq_o in H0. 
rewrite <-H3 in H0. elim (VertexSet.empty_1 H0).
auto.
auto.

set (tmp := fold_left f' l m) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec y a). rewrite MapFacts.add_eq_o in H3.
destruct (Vertex.eq_dec y (fst_ext e)).
unfold adj_set in H0.
rewrite MapFacts.add_eq_o in H0.
elim (VertexSet.diff_2 H0).
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)). assumption.
intuition.
unfold adj_set in H0. rewrite MapFacts.add_neq_o in H0.
rewrite <-H2 in H0.
inversion H3; subst; clear H3.
rewrite H4 in H0. clear H4.
destruct (Vertex.eq_dec x (fst_ext e)).
elim (VertexSet.remove_1 (Vertex.eq_sym e1) H0).
apply (merge_conflicts e g Haff Hin x y); auto.
unfold adj_set. rewrite (MapFacts.find_o _ e0). apply (VertexSet.remove_3 H0).
auto.
intuition.

rewrite MapFacts.add_neq_o in H3.
unfold adj_set in IHl.
destruct (Vertex.eq_dec y (fst_ext e)).
rewrite MapFacts.add_eq_o in IHl.
unfold adj_set in H0.
rewrite MapFacts.add_eq_o in H0.
apply IHl. assumption. intro.
generalize (HH H1). intro.
inversion H5; subst.
elim (n H7).
assumption.
intuition.
intuition.
rewrite MapFacts.add_neq_o in IHl. rewrite <-H3 in IHl.
unfold adj_set in H0. rewrite MapFacts.add_neq_o in H0.
rewrite <-H2 in H0.
apply IHl. rewrite <-H4. assumption.
intro. generalize (HH H1). intro.
inversion H5; subst.
elim (n H7).
assumption.
auto.
auto.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H1. auto. auto.
Qed.

Lemma simple_graph_merge_map : forall e g,
aff_edge e ->
In_graph_edge e g ->
forall x y,
VertexSet.In x (adj_set y (imap_merge e g)) /\
VertexSet.In x (adj_set y (pmap_merge e g (imap_merge e g))) ->
False.

Proof.
exact (fun e g H H0 x y H1 =>
 (resolve_conflicts_map_3 x y e g H H0 H1)).
Qed.

Lemma sym_map_merge_pmap : forall e g x y,
aff_edge e ->
In_graph_edge e g ->
VertexSet.In x (adj_set y (map_merge e (pmap g))) ->
VertexSet.In y (adj_set x (map_merge e (pmap g))).

Proof.
intros e g x y Haff Hin H.
apply sym_map_merge_map with (g:=g); auto.
apply (sym_pmap g).
intros.
apply (not_eq_extremities_map_merge a b e (pmap g)). 
intros. apply (not_eq_extremities g). right. assumption. assumption.

assert (~Vertex.eq y (snd_ext e)) as Hy.
intro.
assert (VertexSet.In y (VertexSet.remove (snd_ext e) (V g))).
apply (pmap_merge_domain_1 y _ _ Hin).
rewrite MapFacts.in_find_iff. intro.
unfold adj_set in H. rewrite H1 in H. elim (VertexSet.empty_1 H).
elim (VertexSet.remove_1 (Vertex.eq_sym H0) H1).

intro.
unfold map_merge in H.

set (f :=  (fun (y : VertexSet.elt) (m' : VertexMap.t VertexSet.t) =>
                   VertexMap.add y
                     (VertexSet.add (fst_ext e)
                        (VertexSet.remove (snd_ext e) (adj_set y (pmap g))))
                     m')) in *.
set (s := (VertexSet.union
                  (VertexSet.remove (snd_ext e)
                     (adj_set (fst_ext e) (pmap g)))
                  (VertexSet.remove (fst_ext e)
                     (adj_set (snd_ext e) (pmap g))))) in *.
set (s' := adj_set (snd_ext e) (pmap g)) in *.

unfold adj_set in H.
rewrite MapFacts.remove_neq_o in H.
destruct (Vertex.eq_dec y (fst_ext e)).
rewrite MapFacts.add_eq_o in H.
unfold s in H.
destruct (VertexSet.union_1 H).
elim (VertexSet.remove_1 (Vertex.eq_sym H0) H1).
generalize (VertexSet.remove_3 H1). clear H1. intro H1.
unfold s' in H1.

elim (not_eq_extremities g x (snd_ext e)).
right. assumption.
assumption.
intuition.
rewrite MapFacts.add_neq_o in H.

rewrite VertexSet.fold_1 in H.
set (f' := fun a e => f e a) in *.
generalize VertexSet.elements_1. intro.
generalize (H1 (VertexSet.remove (fst_ext e) s') y). clear H1. intro H1.
induction (VertexSet.elements (VertexSet.remove (fst_ext e) s')).
simpl in H.
unfold s' in H1.
assert (InA Vertex.eq y nil).
apply H1.
apply VertexSet.remove_2. auto.
apply (sym_pmap g). rewrite <-H0. assumption. inversion H2.

cut (EqualSetMap (fold_left f' (a :: l) (pmap g)) (f' (fold_left f' l (pmap g)) a)). intro.
generalize (H2 y). clear H2. intro H2. simpl in H. inversion H2; clear H2.
rewrite <-H4 in *.
elim (VertexSet.empty_1 H).
set (tmp := fold_left f' l (pmap g)) in *.
unfold f' in H4. unfold f in H4.
destruct (Vertex.eq_dec y a).
rewrite MapFacts.add_eq_o in H4.
rewrite <-H3 in *. clear H3. inversion H4. subst. clear H4.
rewrite H5 in H. clear H5.
destruct (proj1 (Props.Dec.F.add_iff _ _ _) H).
elim (In_graph_edge_diff_ext _ _ Hin).
apply Vertex.eq_trans with (y := x); auto.
elim (VertexSet.remove_1 (Vertex.eq_sym H0) H2).
intuition.
rewrite MapFacts.add_neq_o in H4. rewrite <-H4 in IHl.
apply IHl.
rewrite <-H5. rewrite <-H3 in H. assumption.
intro. generalize (H1 H2). clear H2. intro H2.
inversion H2; subst.
elim (n0 H7).
assumption.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H2. auto. auto.

auto.
auto.

intro.
assert (VertexSet.In y (VertexSet.remove (snd_ext e) (V g))).
apply (pmap_merge_domain_1 y _ _ Hin).
rewrite MapFacts.in_find_iff. intro.
unfold adj_set in H. rewrite H1 in H. elim (VertexSet.empty_1 H).
elim (VertexSet.remove_1 (Vertex.eq_sym H0) H1).
Qed.

Lemma sym_resolve : forall x y e g,
aff_edge e ->
In_graph_edge e g ->
VertexSet.In x (adj_set y (resolve_conflicts (fst_ext e) (map_merge e (pmap g))
                                             (adj_set (fst_ext e) (map_merge e (pmap g)))
                                             (adj_set (fst_ext e) (imap_merge e g)))) ->
VertexSet.In y (adj_set x (resolve_conflicts (fst_ext e) (map_merge e (pmap g))
                                             (adj_set (fst_ext e) (map_merge e (pmap g)))
                                             (adj_set (fst_ext e) (imap_merge e g)))).

Proof.
unfold resolve_conflicts; intros x y e g p q H.
set (f := (fun (x0 : VertexSet.elt) (m : VertexMap.t VertexSet.t) =>
            VertexMap.add x0
              (VertexSet.remove (fst_ext e)
                 (adj_set x0 (map_merge e (pmap g)))) m)) in *.
set (s := (VertexSet.diff (adj_set (fst_ext e) (map_merge e (pmap g)))
           (adj_set (fst_ext e) (imap_merge e g)))) in *.
set (s' :=  (VertexSet.inter (adj_set (fst_ext e) (map_merge e (pmap g)))
              (adj_set (fst_ext e) (imap_merge e g)))) in *.
set (m := map_merge e (pmap g)) in *.
rewrite VertexSet.fold_1 in *.
set (f' := fun a e => f e a) in *.
generalize VertexSet.elements_1. intro.
generalize (H0 s' y). clear H0. intro HH.
generalize VertexSet.elements_2. intro.
generalize (H0 s'). clear H0. intro HHH.
induction (VertexSet.elements s'). simpl in *.
destruct (Vertex.eq_dec x (fst_ext e)).
unfold adj_set. rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec y (fst_ext e)).
unfold adj_set in H. rewrite MapFacts.add_eq_o in H.
generalize (VertexSet.diff_1 H). intro H0.
rewrite e0 in H0.
unfold m in H0. unfold map_merge in H0.
unfold adj_set in H0.
rewrite MapFacts.remove_neq_o in H0.
rewrite MapFacts.add_eq_o in H0.
fold (adj_set (fst_ext e) (pmap g)) in H0.
fold (adj_set (snd_ext e) (pmap g)) in H0.
destruct (VertexSet.union_1 H0).
generalize (VertexSet.remove_3 H1). intro.
elim (not_eq_extremities g (fst_ext e) (fst_ext e)). right. auto.
intuition.
elim (VertexSet.remove_1 (Vertex.eq_refl _) H1).
intuition.
apply (In_graph_edge_diff_ext _ _ q). intuition.
unfold adj_set in H. rewrite MapFacts.add_neq_o in H.
fold (adj_set y m) in H.
destruct (Props.In_dec y (adj_set (fst_ext e) (imap_merge e g))).
assert (InA Vertex.eq y nil).
apply HH. apply VertexSet.inter_3.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
apply (sym_map_merge_pmap e g _ _ p q H). assumption. inversion H0.
apply VertexSet.diff_3.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
apply (sym_map_merge_pmap e g _ _ p q H). assumption.
auto.
intuition.

unfold adj_set. rewrite MapFacts.add_neq_o.
fold (adj_set x m).
destruct (Vertex.eq_dec y (fst_ext e)).
unfold adj_set in H. rewrite MapFacts.add_eq_o in H.
apply (sym_map_merge_pmap e g _ _ p q).
unfold adj_set. rewrite (MapFacts.find_o _ e0).
apply (VertexSet.diff_1 H).
intuition.
unfold adj_set in H. rewrite MapFacts.add_neq_o in H.
apply (sym_map_merge_pmap e g _ _ p q H).
auto.
auto.

cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
destruct (Vertex.eq_dec x (fst_ext e)).
unfold adj_set. rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec y (fst_ext e)).
unfold adj_set in H. rewrite MapFacts.add_eq_o in H.
rewrite e1. rewrite <-e0. assumption.
intuition.
unfold adj_set in H. rewrite MapFacts.add_neq_o in H.
generalize (H0 y). simpl in H. intro H1. inversion H1; clear H1.
rewrite <-H3 in H.
elim (VertexSet.empty_1 H).
rewrite <-H2 in H. clear H2.
set (tmp := fold_left f' l m) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec y a). rewrite MapFacts.add_eq_o in H3.
inversion H3; subst; clear H3.
rewrite H4 in H. elim (VertexSet.remove_1 (Vertex.eq_sym e0) H).
intuition.
rewrite MapFacts.add_neq_o in H3.
unfold adj_set in IHl. rewrite MapFacts.add_neq_o in IHl. 
                       rewrite MapFacts.add_eq_o in IHl.
rewrite <-H3 in IHl.
apply IHl. rewrite <-H4. assumption.
intros. generalize (HH H1). intro.
inversion H2; subst.
elim (n0 H6).
assumption.
auto.
intuition.
auto.
auto.
auto.
intuition.

unfold adj_set. rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec y (fst_ext e)).
unfold adj_set in H. rewrite MapFacts.add_eq_o in H.
generalize (H0 x). intro H1. inversion H1; subst; clear H1.
set (tmp := fold_left f' l m) in *.
unfold f' in H4. unfold f in H4.
destruct (Vertex.eq_dec x a).
rewrite MapFacts.add_eq_o in H4. congruence. intuition.
destruct (Vertex.eq_dec y a).
assert (VertexSet.In y s'). apply HHH.
left. auto.
rewrite e0 in H1.
unfold s' in H1.
elim (not_eq_extremities_merge_map e g p (fst_ext e) (fst_ext e)).
left. apply (VertexSet.inter_2 H1).
intuition.
rewrite MapFacts.add_neq_o in H4.
unfold adj_set in IHl. rewrite MapFacts.add_eq_o in IHl. 
                       rewrite MapFacts.add_neq_o in IHl.
rewrite <-H4 in IHl.
assert (VertexSet.In y VertexSet.empty).
apply IHl. assumption.
intro. generalize (HH H1). intro.
inversion H2; subst.
elim (n1 H6). auto.
intros. apply HHH. right. auto.
elim (VertexSet.empty_1 H1).
auto.
intuition.
auto.

unfold adj_set in IHl. rewrite MapFacts.add_eq_o in IHl. 
                       rewrite MapFacts.add_neq_o in IHl.
simpl. rewrite <-H2. rewrite H4.
set (tmp := fold_left f' l m) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec x a).
rewrite MapFacts.add_eq_o in H3.
inversion H3; subst; clear H3.
assert (VertexSet.In x s').
apply HHH. left. auto.
elim (VertexSet.diff_2 H (VertexSet.inter_2 H1)). intuition.
rewrite MapFacts.add_neq_o in H3.
rewrite <-H3 in IHl.
destruct (Vertex.eq_dec y a).
assert (VertexSet.In y s'). apply HHH. left. intuition.
unfold s' in H1.
elim (not_eq_extremities_merge_map e g p (fst_ext e) (fst_ext e)).
left. rewrite e0 in H1. apply (VertexSet.inter_2 H1). intuition.

apply IHl.
assumption.
intro. generalize (HH H1). intro.
inversion H5; subst.
elim (n1 H7).
auto.

intros. apply HHH. right. auto.
auto.
auto.
intuition.
intuition.

unfold adj_set in H. rewrite MapFacts.add_neq_o in H.
simpl in H.
unfold adj_set in IHl. rewrite MapFacts.add_neq_o in IHl.
                       rewrite MapFacts.add_neq_o in IHl.
generalize (H0 y). intro H1. inversion H1; clear H1.
rewrite <-H3 in H. elim (VertexSet.empty_1 H).
rewrite <-H2 in H.
set (tmp := fold_left f' l m) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec y a). rewrite MapFacts.add_eq_o in H3.
inversion H3; subst; clear H3.
generalize H. clear H. intro H. rewrite H4 in H.
generalize (VertexSet.remove_3 H). clear H. intro H.
unfold adj_set in H. rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)) in H.
fold (adj_set y m) in H.
generalize (sym_map_merge_pmap e g _ _ p q H). clear H. intro H.
fold m in H.
clear IHl H0 H2 HH HHH.

set (l' := a :: l) in *.
induction l'.  simpl. assumption.

(*
 unfold f'. unfold f.
destruct (Vertex.eq_dec x a). rewrite MapFacts.add_eq_o.
apply VertexSet.remove_2; auto.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)). auto.
auto.
rewrite MapFacts.add_neq_o. assumption.
auto.
*)

cut (EqualSetMap (fold_left f' (a0 :: l') m) (f' (fold_left f' l' m) a0)). intro.
generalize (H0 x). clear H0. intro H0. simpl. inversion H0; clear H0.
set (tmp' := fold_left f' l' m) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec x a0).
rewrite MapFacts.add_eq_o in H3. congruence. intuition.
rewrite MapFacts.add_neq_o in H3.
rewrite <-H3 in IHl'. elim (VertexSet.empty_1 IHl').
auto.
set (tmp' := fold_left f' l' m) in *.
unfold f' in H2. unfold f in H2.
destruct (Vertex.eq_dec x a0).
rewrite MapFacts.add_eq_o in H2. inversion H2; subst; clear H2.
rewrite H3. apply VertexSet.remove_2. auto.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)). assumption.
intuition.
rewrite MapFacts.add_neq_o in H2.
rewrite <-H2 in IHl'.
rewrite H3. auto.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e2)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
apply VertexSet.eq_refl. intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s1); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a1).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H0. auto. intuition.

intuition.
rewrite MapFacts.add_neq_o in H3.
rewrite <-H3 in IHl.

generalize (H0 x). intro. inversion H1; clear H1.
unfold f' in H7. unfold f in H7.
destruct (Vertex.eq_dec x a).
rewrite MapFacts.add_eq_o in H7. congruence. intuition.
rewrite MapFacts.add_neq_o in H7.
rewrite <-H7 in IHl. simpl. rewrite <-H6.
apply IHl.
rewrite <-H4. auto.

intro. generalize (HH H1). intro.
inversion H5; subst.
elim (n1 H9).
auto.

intros. apply HHH. right. auto.
auto.

unfold f' in H6. unfold f in H6.
destruct (Vertex.eq_dec x a).
rewrite MapFacts.add_eq_o in H6.
inversion H6; subst; clear H6.
simpl. rewrite <-H5.
rewrite H7.
apply VertexSet.remove_2. auto.

case_eq (VertexMap.find x tmp); intros.
rewrite H1 in IHl.
assert (VertexSet.In y t0).
apply IHl. rewrite <-H4. assumption.

intro. generalize (HH H6). intro.
inversion H8; subst.
elim (n1 H10).
auto.

intros. apply HHH. right. auto.
clear H HH HHH IHl H0 H4 H2 H3 H5 H7.
assert (eq_set_option (Some t0) (VertexMap.find x tmp)).
rewrite H1. constructor. apply VertexSet.eq_refl. clear H1.
unfold tmp in H.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
fold (adj_set x m).
induction l. simpl in H. inversion H.
unfold adj_set. rewrite <-H1. rewrite <-H2. auto.

cut (EqualSetMap (fold_left f' (a0 :: l) m) (f' (fold_left f' l m) a0)). intro.
generalize (H0 x). clear H0. intro H0. simpl in H. inversion H0; subst.
rewrite <-H2 in H. inversion H.
set (tmp' := fold_left f' l m) in *.
unfold f' in H2. unfold f in H2.
destruct (Vertex.eq_dec x a0).
rewrite MapFacts.add_eq_o in H2.
inversion H; subst. rewrite <-H1 in H5.
inversion H5; subst; clear H5.
rewrite H7 in H6. rewrite H3 in H6. inversion H2; subst; clear H2 H3 H7.
unfold adj_set. rewrite (MapFacts.find_o _ e1). apply (VertexSet.remove_3 H6). intuition.
rewrite MapFacts.add_neq_o in H2. rewrite <-H2 in IHl.
apply IHl. constructor. rewrite <-H1 in H. inversion H; subst.
rewrite H7. auto.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e2)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
apply VertexSet.eq_refl. intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s2); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a1).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H0. auto. auto.

rewrite H1 in IHl.
assert (VertexSet.In y VertexSet.empty).
apply IHl.
rewrite <-H4. auto.
intro. generalize (HH H6). intro.
inversion H8; subst.
elim (n1 H10).
auto.

intros. apply HHH. right. auto.
elim (VertexSet.empty_1 H6). intuition.

rewrite MapFacts.add_neq_o in H6.
rewrite <-H6 in IHl. simpl. rewrite <-H5.
rewrite H7. apply IHl.
rewrite <-H4. auto.
intro. generalize (HH H1). intro.
inversion H8; subst.
elim (n1 H10).
auto.

intros. apply HHH. right. auto.
auto.
auto.
auto.
auto.
auto.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
apply VertexSet.eq_refl. intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H0. auto. auto.
Qed.

Lemma sym_pmap_merge_map e g :
aff_edge e ->
In_graph_edge e g ->
forall x y,
VertexSet.In x (adj_set y (pmap_merge e g (imap_merge e g))) ->
VertexSet.In y (adj_set x (pmap_merge e g (imap_merge e g))).

Proof.
intros. apply sym_resolve; assumption.
Qed.

Definition merge e g 
           (q : In_graph_edge e g)
           (p : aff_edge e) :=
 let im := imap_merge e g in
 let pm := pmap_merge e g im in
 Make_Graph (VertexSet.remove (snd_ext e) (V g))
            im
            pm
            (extremities_in_merge_imap e g q)
            (extremities_in_merge_pmap e g p q)
            (simple_graph_merge_map e g p q)
            (sym_imap_merge_map e g p q)
            (sym_pmap_merge_map e g p q)
            (not_eq_extremities_merge_map e g p).

Lemma In_graph_dec : forall v g,
{In_graph v g} + {~In_graph v g}.

Proof.
exact (fun v g => Props.In_dec v (V g)).
Qed.

Definition pmap_delete_preferences v g :=
let pm := pmap g in
let m := VertexMap.add v VertexSet.empty pm in
VertexSet.fold
          (fun y m' => VertexMap.add y (VertexSet.remove v (adj_set y pm)) m')
          (adj_set v pm)
          m.

Lemma delete_preference_sub : forall x v g,
VertexSet.Subset (adj_set x (pmap_delete_preferences v g))
                 (adj_set x (pmap g)).

Proof.
unfold VertexSet.Subset;intros.
unfold pmap_delete_preferences in H.
rewrite VertexSet.fold_1 in H.

generalize VertexSet.elements_2.
intro H0. generalize (H0 (adj_set v (pmap g))). clear H0. intro H0.
induction (VertexSet.elements (adj_set v (pmap g))); intros.
simpl in H.
unfold adj_set in H.
destruct (Vertex.eq_dec v x).
rewrite InterfFacts.add_eq_o in H.
elim (VertexSet.empty_1 H).
assumption.
rewrite InterfFacts.add_neq_o in H. auto.
assumption.
cut (EqualSetMap
       (fold_left
          (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
           VertexMap.add e (VertexSet.remove v (adj_set e (pmap g))) a) (a0 :: l)
          (VertexMap.add v VertexSet.empty (pmap g)))
       (VertexMap.add a0
          (VertexSet.remove v
             (adj_set a0 (pmap g)))
          (fold_left
             (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
              VertexMap.add e (VertexSet.remove v (adj_set e (pmap g))) a) l
             (VertexMap.add v VertexSet.empty (pmap g))))).

intro.
assert (VertexSet.In a (adj_set x
          (VertexMap.add a0
          (VertexSet.remove v
             (adj_set a0 (pmap g)))
          (fold_left
             (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
              VertexMap.add e (VertexSet.remove v (adj_set e (pmap g))) a) l
             (VertexMap.add v VertexSet.empty (pmap g)))))).
unfold EqualSetMap in H1. generalize (H1 x). intro H2.
inversion H2.
unfold adj_set. unfold adj_set in H5. rewrite <-H5.
unfold adj_set in *. simpl in H. rewrite <-H4 in H.
assumption.
unfold adj_set in *. rewrite <-H4. 
unfold adj_set in *. simpl in H. rewrite <-H3 in H.
rewrite <-H5. assumption.
generalize (H1 x). clear H1. intro H1. inversion H1.
simpl in H. unfold adj_set in H. unfold adj_set in H4. rewrite <-H4 in H.
elim (VertexSet.empty_1 H).
clear H1.
destruct (Vertex.eq_dec x a0).
unfold adj_set in H2. rewrite InterfFacts.add_eq_o in H2.
generalize (VertexSet.remove_3 H2). unfold adj_set.
rewrite (InterfFacts.find_o _ e). auto. intuition.
apply IHl.
rewrite InterfFacts.add_neq_o in H4.
unfold adj_set in *. rewrite <-H4.
rewrite <-H5. simpl in H. rewrite <-H3 in *.
assumption.
auto.
intuition.

apply fold_left_assoc_map.

intros.
unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 z).
rewrite InterfFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y).
rewrite InterfFacts.add_eq_o.
constructor.
generalize (Vertex.eq_trans (Vertex.eq_sym e0) e). intro HH.
unfold adj_set.
rewrite (InterfFacts.find_o _ HH). apply VertexSet.eq_refl. intuition.

rewrite InterfFacts.add_neq_o.
rewrite InterfFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.

rewrite InterfFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y).
rewrite InterfFacts.add_eq_o.
rewrite InterfFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.

intros.
unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 y).
rewrite InterfFacts.add_eq_o.
rewrite InterfFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite InterfFacts.add_neq_o.
rewrite InterfFacts.add_neq_o.
rewrite InterfFacts.add_neq_o.
apply EqualSetMap_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 a1).
rewrite InterfFacts.add_eq_o.
rewrite InterfFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite InterfFacts.add_neq_o.
rewrite InterfFacts.add_neq_o.
apply (H1 x0).
auto.
auto.
Qed.

Lemma in_pmap_delete_in : forall x v g,
In_graph v g ->
VertexMap.In x (pmap_delete_preferences v g) ->
VertexMap.In x (pmap g).

Proof.
intros x v g H1 H.
unfold pmap_delete_preferences in H.
rewrite VertexSet.fold_1 in H.

generalize VertexSet.elements_2. intro HH.
generalize (HH (adj_set v (pmap g))). clear HH. intro HH.

induction (VertexSet.elements (adj_set v (pmap g))); intros.
simpl in H.
destruct (proj1 (InterfFacts.add_in_iff _ _ _ _) H).
apply (proj2 (extremities_pmap g x)).
rewrite <-H0. assumption.
assumption.

cut (EqualSetMap
       (fold_left
          (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
           VertexMap.add e (VertexSet.remove v (adj_set e (pmap g))) a) (a :: l)
          (VertexMap.add v VertexSet.empty (pmap g)))
       (VertexMap.add a
          (VertexSet.remove v
             (adj_set a (pmap g)))
          (fold_left
             (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
              VertexMap.add e (VertexSet.remove v (adj_set e (pmap g))) a) l
             (VertexMap.add v VertexSet.empty (pmap g))))). intro.
unfold EqualSetMap in H0.

generalize (proj1 (InterfFacts.in_find_iff _ _) H). clear H. intro H.
generalize (H0 x). intro H2.
inversion H2.
unfold adj_set in *. simpl in H. rewrite <-H4 in H.
elim H. auto.
clear H2.
destruct (Vertex.eq_dec x a).
rewrite InterfFacts.add_eq_o in H4.
apply (proj2 (InterfFacts.in_find_iff _ _)).
assert (VertexSet.In v (adj_set x (pmap g))).
apply (sym_pmap g).
apply HH. left. auto.
unfold adj_set in H2.
destruct (VertexMap.find x (pmap g)).
intro Helim. inversion Helim.
elim (VertexSet.empty_1 H2). intuition.
rewrite InterfFacts.add_neq_o in H4.
apply IHl.
apply (proj2 (InterfFacts.in_find_iff _ _)).
rewrite <-H4. intro Helim. inversion Helim.
intuition.
auto.

apply fold_left_assoc_map.
intros.
unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 z).
rewrite InterfFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y).
rewrite InterfFacts.add_eq_o.
constructor.
generalize (Vertex.eq_trans (Vertex.eq_sym e0) e). intro HHH.
unfold adj_set.
rewrite (InterfFacts.find_o _ HHH). apply VertexSet.eq_refl. intuition.

rewrite InterfFacts.add_neq_o.
rewrite InterfFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.

rewrite InterfFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y).
rewrite InterfFacts.add_eq_o.
rewrite InterfFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.

intros.
unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 y).
rewrite InterfFacts.add_eq_o.
rewrite InterfFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite InterfFacts.add_neq_o.
rewrite InterfFacts.add_neq_o.
rewrite InterfFacts.add_neq_o.
apply EqualSetMap_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 a0).
rewrite InterfFacts.add_eq_o.
rewrite InterfFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite InterfFacts.add_neq_o.
rewrite InterfFacts.add_neq_o.
apply (H0 x0).
auto.
auto.
Qed.

Lemma extremities_in_delete_preferences_imap (v : Vertex.t) g :
forall x,
VertexMap.In x (imap g) <-> VertexSet.In x (V g).

Proof.
exact (fun v g => extremities_imap g).
Qed.

Lemma extremities_in_delete_preferences_pmap v g :
In_graph v g ->
(forall x,
VertexMap.In x (pmap_delete_preferences v g) <->
VertexSet.In x (V g)).

Proof.
split; intros.
apply (proj1 (extremities_pmap g x)).
apply in_pmap_delete_in with (v:=v); auto.

unfold pmap_delete_preferences.
set (f := (fun (y : VertexSet.elt) (m' : VertexMap.t VertexSet.t) =>
      VertexMap.add y (VertexSet.remove v (adj_set y (pmap g))) m')) in *.
set (m := VertexMap.add v VertexSet.empty (pmap g)).
rewrite VertexSet.fold_1.
induction (VertexSet.elements (adj_set v (pmap g))). simpl.
unfold m.
rewrite MapFacts.in_find_iff.
destruct (Vertex.eq_dec x v).
rewrite MapFacts.add_eq_o.
congruence. intuition.
rewrite MapFacts.add_neq_o.
generalize (proj2 (extremities_pmap g x) H0).
rewrite MapFacts.in_find_iff. auto.
auto.
set (h := (fun (a0 : VertexMap.t VertexSet.t) (e : VertexSet.elt) => f e a0)) in *.

cut (EqualSetMap (fold_left h (a :: l) m) (h (fold_left h l m) a)). intro.
generalize (H1 x). clear H1. intro H1.
inversion H1.
set (tmp := fold_left h l m) in *.
unfold h in H4.
unfold f in H4.
destruct (Vertex.eq_dec x a).
rewrite MapFacts.add_eq_o in H4.
congruence. intuition.
rewrite MapFacts.add_neq_o in H4.
rewrite MapFacts.in_find_iff in IHl. rewrite <-H4 in IHl.
congruence. intuition.
simpl. rewrite MapFacts.in_find_iff. rewrite <-H2. congruence.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold h. unfold f. intros.
destruct (Vertex.eq_dec x0 z).
rewrite InterfFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y).
rewrite InterfFacts.add_eq_o.
constructor.
generalize (Vertex.eq_trans (Vertex.eq_sym e0) e). intro HHH.
unfold adj_set.
rewrite (InterfFacts.find_o _ HHH). apply VertexSet.eq_refl.
intuition.

rewrite InterfFacts.add_neq_o.
rewrite InterfFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.

rewrite InterfFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y).
rewrite InterfFacts.add_eq_o.
rewrite InterfFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.

rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s); constructor.
apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

intros.
unfold EqualSetMap. unfold h. unfold f. intros.
destruct (Vertex.eq_dec x0 a0).
rewrite InterfFacts.add_eq_o.
rewrite InterfFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite InterfFacts.add_neq_o.
rewrite InterfFacts.add_neq_o.
apply H1. auto. auto.
Qed.

(*
Lemma extremities_in_delete_preferences v g :
forall x,
VertexMap.In x (imap g) \/ 
VertexMap.In x (pmap_delete_preferences v g) <->
VertexSet.In x (V g).

Proof.
split; intros.
destruct (Vertex.eq_dec v x).
apply (proj1 (extremities g x)).
destruct H;[left|right].
assumption.
apply in_pmap_delete_in with (v:=v); auto.

Qed.
*)

Lemma simple_graph_delete_preferences v g : forall x y,
VertexSet.In x (adj_set y (imap g)) /\
VertexSet.In x (adj_set y (pmap_delete_preferences v g)) -> False.

Proof.
intros.
destruct H.
generalize (delete_preference_sub _ _ _ _ H0). clear H0. intro H0.
apply (simple_graph g x y). intuition.
Qed.

Lemma sym_imap_delete_preferences (v : Vertex.t) g :
forall x y,
VertexSet.In x (adj_set y (imap g)) ->
VertexSet.In y (adj_set x (imap g)).

Proof.
exact (fun v g => sym_imap g).
Qed.

Lemma in_adj_delete_preference_not_eq_1 : forall x y v g,
VertexSet.In x (adj_set y (pmap_delete_preferences v g)) ->
~Vertex.eq y v.

Proof.
intros.
unfold pmap_delete_preferences in H.
rewrite VertexSet.fold_1 in H.
set (f:= (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
             VertexMap.add e (VertexSet.remove v (adj_set e (pmap g))) a)) in *.
set (l := VertexSet.elements (adj_set v (pmap g))) in *.
generalize VertexSet.elements_2. intro HH.
generalize (HH (adj_set v (pmap g))). clear HH. intro HH.
fold l in HH.
assert (forall z, In z l -> ~Vertex.eq v z) as Hneq.
clear H.
intros. intro H0.
induction l. inversion H.
simpl in H. destruct H. subst.
assert (VertexSet.In v (adj_set v (pmap g))).
apply HH. left. auto.
elim (not_eq_extremities g v v).
right. assumption.
auto.
apply IHl.
intros. apply HH. auto.
assumption.

induction l. simpl in H.
unfold adj_set in H. intro Helim.
rewrite MapFacts.add_eq_o in H.
elim (VertexSet.empty_1 H). intuition.
set (s := VertexMap.add v VertexSet.empty (pmap g)) in *.

assert (EqualSetMap (fold_left f (a :: l) s) (f (fold_left f l s) a)).
apply fold_left_assoc_map.

unfold f. unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
apply Props.Equal_remove.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_trans (Vertex.eq_sym e) e0)).
apply VertexSet.eq_refl. intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor.
apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold f. unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H0.
auto.
auto.

intro Helim.
cut (VertexSet.In x (adj_set y (f (fold_left f l s) a))).
set (tmp := fold_left f l s) in *.
intro H1.
unfold f in H1.
generalize (H0 x). clear H0. intro H0.
unfold adj_set in H1. inversion H0.
rewrite <-H4 in *.
destruct (Vertex.eq_dec y a).
elim (Hneq a). left. auto.
apply (Vertex.eq_trans (Vertex.eq_sym Helim) e).
rewrite MapFacts.add_neq_o in H1.
apply IHl.
assumption.
intros. apply HH. auto.
intros. apply Hneq. right. auto.
assumption.
auto.

rewrite <-H3 in *.
destruct (Vertex.eq_dec y a).
elim (Hneq a). left. auto.
apply (Vertex.eq_trans (Vertex.eq_sym Helim) e).
rewrite MapFacts.add_neq_o in H1.
apply IHl.
assumption.
intros. apply HH. auto.
intros. apply Hneq. right. auto.
assumption.
auto.

clear HH Hneq IHl.
unfold adj_set in H. unfold adj_set.
generalize (H0 y). clear H0. intro H0.
simpl in H.
inversion H0; subst.
rewrite <-H3 in *.
simpl in H. rewrite <-H2 in *.
elim (VertexSet.empty_1 H).
rewrite <-H1 in *.
rewrite <-H2 in *.
rewrite <-H3. assumption.
Qed.

Lemma in_adj_delete_preference_not_eq_2 : forall x y v g,
VertexSet.In x (adj_set y (pmap_delete_preferences v g)) ->
~Vertex.eq x v.

Proof.
intros. intro Helim. generalize H. intro Hcopy.
unfold pmap_delete_preferences in H.
rewrite VertexSet.fold_1 in H.
set (f:= (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
             VertexMap.add e (VertexSet.remove v (adj_set e (pmap g))) a)) in *.
generalize VertexSet.elements_1. intro.
generalize (H0 (adj_set v (pmap g)) y). clear H0. intro HH.
set (l := VertexSet.elements (adj_set v (pmap g))) in *.
induction l. simpl in H.
unfold adj_set in H.
rewrite MapFacts.add_neq_o in H.
generalize (sym_pmap g). intro Hsym.
generalize (Hsym _ _ H). intro H0.
unfold adj_set in H0.
rewrite (MapFacts.find_o _ Helim) in H0.
generalize (HH H0). intro H1. inversion H1.
generalize (in_adj_delete_preference_not_eq_1 x y v g Hcopy). auto.
set (s := VertexMap.add v VertexSet.empty (pmap g)) in *.

assert (EqualSetMap (fold_left f (a :: l) s) (f (fold_left f l s) a)).
apply fold_left_assoc_map.

unfold f. unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
apply Props.Equal_remove.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_trans (Vertex.eq_sym e) e0)).
apply VertexSet.eq_refl. intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor.
apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold f. unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H0.
auto.
auto.

clear Hcopy.
cut (VertexSet.In x (adj_set y (f (fold_left f l s) a))).
set (tmp := fold_left f l s) in *.
intro H1.
unfold f in H1. unfold adj_set in H1.
destruct (Vertex.eq_dec y a).
rewrite MapFacts.add_eq_o in H1.
elim (VertexSet.remove_1 (Vertex.eq_sym Helim) H1). intuition.
rewrite MapFacts.add_neq_o in H1.
apply IHl.
assumption.
intro. generalize (HH H2). intro H3.
inversion H3; subst.
elim (n H5).
assumption.
auto.

unfold adj_set.
generalize (H0 y). clear H0. intro H0.
inversion H0; subst.
simpl in H. unfold adj_set in H. rewrite <-H2 in H.
assumption.
simpl in H. unfold adj_set in H. rewrite <-H1 in H.
rewrite <-H3. assumption.
Qed.

Lemma sym_pmap_delete_preferences (v : Vertex.t) g :
forall x y,
VertexSet.In x (adj_set y (pmap_delete_preferences v g)) ->
VertexSet.In y (adj_set x (pmap_delete_preferences v g)).

Proof.
intros.
generalize (in_adj_delete_preference_not_eq_1 x y v g H). intro Hneqy.
generalize (in_adj_delete_preference_not_eq_2 x y v g H). intro Hneqx.
generalize (delete_preference_sub y v g x H). intro HH.
generalize (sym_pmap g _ _ HH). clear HH. intro HH.
unfold pmap_delete_preferences in *.
rewrite VertexSet.fold_1 in *.
set (f := fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
          VertexMap.add e (VertexSet.remove v (adj_set e (pmap g))) a) in *.
induction (VertexSet.elements (adj_set v (pmap g))).
simpl in *.
destruct (Vertex.eq_dec x v).
destruct (Vertex.eq_dec y v).
unfold adj_set in H. rewrite MapFacts.add_eq_o in H.
elim (VertexSet.empty_1 H).
case_eq (VertexMap.find y (VertexMap.add v VertexSet.empty (pmap g))). intros.
rewrite H0 in H.
rewrite MapFacts.add_eq_o in H0. inversion H0. subst.
elim (VertexSet.empty_1 H). intuition.
rewrite MapFacts.add_eq_o. congruence. intuition.

elim (Hneqx e).

unfold adj_set. rewrite MapFacts.add_neq_o. assumption. intuition.

set (s := VertexMap.add v VertexSet.empty (pmap g)) in *.
assert (EqualSetMap (fold_left f (a :: l) s) (f (fold_left f l s) a)).
apply fold_left_assoc_map.

unfold f. unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
apply Props.Equal_remove.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_trans (Vertex.eq_sym e) e0)).
apply VertexSet.eq_refl. intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor.
apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold f. unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H0.
auto.
auto.

unfold EqualSetMap in H0.
unfold adj_set.
case_eq (VertexMap.find x (fold_left f (a :: l) s)); intros.
generalize (H0 x). intro HH0.
rewrite H1 in HH0. inversion HH0. subst.
set (tmp := fold_left f l s) in *.
unfold adj_set in H.
unfold f in H3.
destruct (Vertex.eq_dec x a).
rewrite MapFacts.add_eq_o in H3.
inversion H3. subst. clear H3.
rewrite H4. apply VertexSet.remove_2.
auto.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e)). assumption.
intuition.

rewrite MapFacts.add_neq_o in H3.
rewrite H4.
cut (VertexSet.In y (adj_set x tmp)).
intro.
unfold adj_set in H2.
rewrite <-H3 in H2. assumption.
apply IHl.
assert (VertexSet.In x (adj_set y (pmap g)) -> VertexSet.In x (adj_set y tmp)).
clear IHl H0 H1 HH0 H4 H3 HH H.
intros.
unfold tmp.
induction l. simpl. unfold s.
unfold adj_set.
rewrite MapFacts.add_neq_o. assumption.
auto.

assert (EqualSetMap (fold_left f (a0 :: l) s) (f (fold_left f l s) a0)).
apply fold_left_assoc_map.

unfold f. unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
apply Props.Equal_remove.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_trans (Vertex.eq_sym e) e0)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor.
apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold f. unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 a1).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H0.
auto.
auto.

generalize (H0 y). clear H0. intro H0.
inversion H0; subst.
unfold adj_set. simpl. rewrite <-H2.
set (tmp' := fold_left f l s) in *.
unfold f in H3.
destruct (Vertex.eq_dec y a0).
rewrite MapFacts.add_eq_o in H3. inversion H3.
intuition.
rewrite MapFacts.add_neq_o in H3.
unfold adj_set in IHl. rewrite <-H3 in IHl.
assumption.
auto.
unfold adj_set. simpl. rewrite <-H1.
rewrite H3.
set (tmp' := fold_left f l s) in *.
unfold f in H2.
destruct (Vertex.eq_dec y a0).
rewrite MapFacts.add_eq_o in H2.
inversion H2. subst. clear H2.
apply VertexSet.remove_2.
auto.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e)).
assumption.
intuition.
rewrite MapFacts.add_neq_o in H2.
assert (VertexSet.In x (adj_set y tmp')).
apply IHl.
unfold adj_set in H4.
rewrite <-H2 in H4. assumption.
auto.
apply H2.
apply (sym_pmap g). assumption.
auto.

generalize (H0 x). clear H0. intro H0.
rewrite H1 in H0. inversion H0. subst.
set (tmp := fold_left f l s) in *.
unfold f in H2.
destruct (Vertex.eq_dec x a).
rewrite MapFacts.add_eq_o in H2.
inversion H2.
intuition.
rewrite MapFacts.add_neq_o in H2.

assert (VertexSet.In y (adj_set x (pmap g)) -> VertexSet.In y (adj_set x tmp)).
clear IHl H H0 HH H2 H1.
intros.
unfold tmp.
induction l. simpl. unfold s.
unfold adj_set.
rewrite MapFacts.add_neq_o. assumption.
intuition.

assert (EqualSetMap (fold_left f (a0 :: l) s) (f (fold_left f l s) a0)).
apply fold_left_assoc_map.

unfold f. unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
apply Props.Equal_remove.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_trans (Vertex.eq_sym e) e0)).
apply VertexSet.eq_refl. intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor.
apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold f. unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x0 a1).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H0.
auto.
auto.

generalize (H0 x). clear H0. intro H0.
inversion H0; subst.
unfold adj_set. simpl. rewrite <-H2.
set (tmp' := fold_left f l s) in *.
unfold f in H3.
destruct (Vertex.eq_dec x a0).
rewrite MapFacts.add_eq_o in H3. inversion H3.
intuition.
rewrite MapFacts.add_neq_o in H3.
unfold adj_set in IHl. rewrite <-H3 in IHl.
assumption.
auto.
unfold adj_set. simpl. rewrite <-H1.
rewrite H3.
set (tmp' := fold_left f l s) in *.
unfold f in H2.
destruct (Vertex.eq_dec x a0).
rewrite MapFacts.add_eq_o in H2.
inversion H2. subst. clear H2.
apply VertexSet.remove_2.
auto.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e)).
assumption.
intuition.
rewrite MapFacts.add_neq_o in H2.
assert (VertexSet.In y (adj_set x tmp')).
apply IHl.
unfold adj_set in H4.
rewrite <-H2 in H4. assumption.
auto.
assert (VertexSet.In y (adj_set x tmp)).
apply H3. assumption.
unfold adj_set in H4.
rewrite <-H2 in H4.
assumption.
auto.
Qed.

Lemma not_eq_extremities_delete_preferences v g :
forall x y,
VertexSet.In x (adj_set y (imap g)) \/
VertexSet.In x (adj_set y (pmap_delete_preferences v g)) ->
~Vertex.eq x y.

Proof.
intros.
apply (not_eq_extremities g).
destruct H;[left|right].
assumption.
apply (delete_preference_sub _ _ _ _ H).
Qed.

Definition delete_preference_edges v g H :=
Make_Graph (V g)
                     (imap g)
                     (pmap_delete_preferences v g)
                     (extremities_in_delete_preferences_imap v g)
                     (extremities_in_delete_preferences_pmap v g H)
                     (simple_graph_delete_preferences v g)
                     (sym_imap_delete_preferences v g)
                     (sym_pmap_delete_preferences v g)
                     (not_eq_extremities_delete_preferences v g).

Definition Prefere x y g :=
exists w, In_graph_edge (x,y,Some w) g.

Definition Interfere x y g :=
In_graph_edge (x,y,None) g.

Definition precolored g :=
VertexSet.filter (fun v => is_precolored v g) (V g).

Parameter mreg_ext : forall x y,
Vertex.eq x y -> is_mreg x = is_mreg y.

Lemma mem_ext : forall x y s,
Vertex.eq x y -> VertexSet.mem x s = VertexSet.mem y s.

Proof.
intros.
case_eq (VertexSet.mem x s); intros.
generalize (VertexSet.mem_2 H0). intro H1.
rewrite H in H1. generalize (VertexSet.mem_1 H1). auto.
case_eq (VertexSet.mem y s); intros.
generalize (VertexSet.mem_2 H1). intro H2.
rewrite <-H in H2. generalize (VertexSet.mem_1 H2). intro H3.
rewrite H3 in H0. inversion H0.
reflexivity.
Qed.

Lemma compat_bool_is_precolored : forall g,
compat_bool Vertex.eq (fun x => is_precolored x g).

Proof.
unfold compat_bool. intros.
unfold is_precolored.
apply mreg_ext. auto.
Qed.

(* Equivalence of predicate and function *)
Lemma precolored_equiv : forall x g,
VertexSet.In x (precolored g) <-> (is_precolored x g = true /\ In_graph x g).

Proof.
split; intros.
split.
apply (VertexSet.filter_2 (compat_bool_is_precolored _) H).
apply (VertexSet.filter_1 (compat_bool_is_precolored _) H).
apply VertexSet.filter_3. apply compat_bool_is_precolored.
unfold is_precolored in H.
case_eq (VertexSet.mem x (V g)); intros.
apply VertexSet.mem_2. assumption. intuition. intuition.
Qed.

Lemma In_graph_aff_edge_in_AE : forall e g,
EdgeSet.In e (AE g) <-> aff_edge e /\ In_graph_edge e g.

Proof.
intros e g. split; intro H.
split.
unfold aff_edge. exists N0. exact (AE_weights g e H).
left. assumption.
destruct H as [H H0].
destruct H0.
assumption.
unfold aff_edge in H. destruct H as [w H].
rewrite (IE_weights g e H0) in H. inversion H.
Qed.

Lemma In_graph_interf_edge_in_IE : forall e g,
EdgeSet.In e (IE g) <-> interf_edge e /\ In_graph_edge e g.

Proof.
intros e g. split; intro H.
split.
exact (IE_weights g e H).
right. assumption.
destruct H as [H H0].
destruct H0.
unfold interf_edge in H.
rewrite (AE_weights g e H0) in H. inversion H.
assumption.
Qed.

(* Spec of Prefere *)
Lemma Prefere_1 : forall e g,
aff_edge e ->
In_graph_edge e g ->
Prefere (fst_ext e) (snd_ext e) g.

Proof.
intros.
unfold Prefere.
destruct H0.
exists N0. rewrite <-(AE_weights g e H0). rewrite <-edge_eq. left. assumption.
generalize (proj1 (In_graph_interf_edge_in_IE _ _) H0). intro H1.
destruct H1 as [H1 _]. unfold interf_edge in H1. unfold aff_edge in H. 
rewrite H1 in H. inversion H. inversion H2.
Qed.

Lemma Prefere_2 : forall x y g,
Prefere x y g ->
In_graph_edge (x,y,Some N0) g.

Proof.
intros.
unfold Prefere in H.
destruct H. 
assert (EdgeSet.In (x,y,Some x0) (AE g)).
rewrite In_graph_aff_edge_in_AE. split. exists x0. auto. auto.
generalize (AE_weights _ _ H0). intro. simpl in H1. rewrite H1 in H. auto.
Qed.

(* spec of Interfere *)
Lemma Interfere_1 : forall e g,
interf_edge e ->
In_graph_edge e g ->
Interfere (fst_ext e) (snd_ext e) g.

Proof.
intros.
unfold Interfere.
destruct H0.
generalize (proj1 (In_graph_aff_edge_in_AE _ _) H0). intro H1.
destruct H1 as [H1 _]. unfold interf_edge in H. unfold aff_edge in H1.
rewrite H in H1. inversion H1. inversion H2.
rewrite <-(IE_weights g e H0). rewrite <-edge_eq. right. assumption.
Qed.

Lemma Interfere_2 : forall x y g,
Interfere x y g ->
In_graph_edge (x,y,None) g.

Proof.
auto.
Qed.

(* Machine registers are registers *)
Lemma In_precolored : forall g ,
VertexSet.Subset (precolored g) (V g).

Proof.
intros.
unfold VertexSet.Subset; intros.
apply (VertexSet.filter_1 (compat_bool_is_precolored _) H).
Qed.

(* specification of remove_vertex *)
Lemma In_remove : forall x r g,
In_graph x g ->
~Vertex.eq x r ->
In_graph x (remove_vertex r g).

Proof.
intros.
unfold remove_vertex. simpl.
apply VertexSet.remove_2; auto.
Qed.

(* A precolored vertex cannot be removed from the graph *)
Lemma not_in_remove : forall r g,
~In_graph r (remove_vertex r g).

Proof.
intros.
unfold remove_vertex.
apply VertexSet.remove_1. apply Vertex.eq_refl.
Qed.

Lemma in_remove_in  : forall x r g,
In_graph x (remove_vertex r g) ->
In_graph x g.

Proof.
intros.
unfold remove_vertex in H.
unfold In_graph in H. simpl in H.
apply (VertexSet.remove_3 H).
Qed.

Add Morphism In_graph : In_graph_m.

Proof.
intros.
unfold In_graph.
rewrite H. reflexivity.
Qed.

(* Probably redundant, TODO get out of interface *)
Lemma precolored_remove_vertex2 : forall x y g,
VertexSet.In x (VertexSet.remove y (precolored g)) <->
VertexSet.In x (precolored (remove_vertex y g)).

Proof.
intros.
split; intros.
generalize (VertexSet.remove_3 H). intro H0.
generalize (VertexSet.filter_1 (compat_bool_is_precolored _) H0). intro.
generalize (VertexSet.filter_2 (compat_bool_is_precolored _) H0). clear H0. intro.
apply VertexSet.filter_3.
apply compat_bool_is_precolored.
unfold remove_vertex. simpl.
apply VertexSet.remove_2. intro. apply (VertexSet.remove_1 H2 H).
assumption.
unfold is_precolored. assumption.
generalize (proj1 (precolored_equiv _ _) H). clear H. intro H. destruct H.
apply VertexSet.remove_2.
intro H1. rewrite <-H1 in H0. elim (not_in_remove _ _ H0).
apply (proj2 (precolored_equiv _ _)).
split.
assumption.
apply in_remove_in with (r:=y). assumption.
Qed.

Lemma In_remove_edge_ : forall e r g,
In_graph_edge e g ->
~incident e r ->
In_graph_edge e (remove_vertex r g).

Proof.
intros.
destruct H;[left|right].
generalize (AE_weights _ _ H). intro Hw.
unfold AE in *.
unfold remove_vertex.
simpl.
rewrite (edge_eq e) in *.
simpl in Hw. rewrite Hw.
apply (proj2 (edgemap_to_edgeset_charac _ _ _ _ (sym_pmap_remove_vertex r g))).
apply imap_remove_1.
intro H1. elim H0. right. auto.
intro H1. elim H0. left. auto.
rewrite Hw in H.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ _ (sym_pmap g)) H).

generalize (IE_weights _ _ H). intro Hw.
unfold IE in *.
unfold remove_vertex.
simpl.
rewrite (edge_eq e) in *.
simpl in Hw. rewrite Hw.
apply (proj2 (edgemap_to_edgeset_charac _ _ _ _ (sym_imap_remove_vertex r g))).
apply imap_remove_1.
intro H1. elim H0. right. auto.
intro H1. elim H0. left. auto.
rewrite Hw in H.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ _ (sym_imap g)) H).
Qed.

Lemma in_remove_in_edge  : forall e r g,
In_graph_edge e (remove_vertex r g) ->
In_graph_edge e g.

Proof.
intros.
destruct H;[left|right].
generalize (AE_weights _ _ H). intro Hw.
unfold AE in *.
unfold remove_vertex in H.
simpl in H.
rewrite (edge_eq e) in *.
simpl in Hw. rewrite Hw.
apply (proj2 (edgemap_to_edgeset_charac _ _ _ _ (sym_pmap g))).
apply imap_remove_3 with (r:=r).
rewrite Hw in H.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ _(sym_pmap_remove_vertex r g)) H).

generalize (IE_weights _ _ H). intro Hw.
unfold IE in *.
unfold remove_vertex in H.
simpl in H.
rewrite (edge_eq e) in *.
simpl in Hw. rewrite Hw.
apply (proj2 (edgemap_to_edgeset_charac _ _ _ _ (sym_imap g))).
apply imap_remove_3 with (r:=r).
rewrite Hw in H.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ _(sym_imap_remove_vertex r g)) H).
Qed.

Lemma not_in_remove_edge : forall e r g,
incident e r ->
~In_graph_edge e (remove_vertex r g).

Proof.
intros. generalize H. intro H0.
destruct (In_graph_edge_dec e g).
assert (In_graph r g) as Hin.
destruct H.
rewrite H. apply (proj1 (In_graph_edge_in_ext _ _ i)).
rewrite H. apply (proj2 (In_graph_edge_in_ext _ _ i)).
intro H1. destruct H1.
generalize (AE_weights _ _ H1). intro Hw.
unfold AE in *.
unfold remove_vertex in H1.
simpl in H1.
rewrite (edge_eq e) in H1.
rewrite Hw in H1. rewrite edge_comm in H1.
generalize (proj1 (edgemap_to_edgeset_charac _ _ _ _ (sym_pmap_remove_vertex r g)) H1).
intro H3.
apply (imap_remove_2 _ _ (pmap g) _ H (sym_pmap g) H3).

generalize (IE_weights _ _ H1). intro Hw.
unfold IE in *.
unfold remove_vertex in H1.
simpl in H1.
rewrite (edge_eq e) in H1.
rewrite Hw in H1. rewrite edge_comm in H1.
generalize (proj1 (edgemap_to_edgeset_charac _ _ _ _ (sym_imap_remove_vertex r g)) H1).
intro H3.
apply (imap_remove_2 _ _ (imap g) _ H (sym_imap g) H3).
intro H1. elim (n (in_remove_in_edge _ _ _ H1)).
Qed.


(* spec of merge *)
Lemma In_merge_in : forall g e x p q,
In_graph x (merge e g p q) -> In_graph x g.

Proof.
intros.
unfold merge in H.
destruct (aff_edge_dec e).
destruct (In_graph_edge_dec e g).
unfold In_graph in H. simpl in H.
apply (VertexSet.remove_3 H).
elim (n p).
elim (n q).
Qed.

(* the second extremity must not be precolored,
   cause it is removed from the graph *)
Lemma merge_1 : forall e g p q,
~In_graph (snd_ext e) (merge e g p q).

Proof.
intros.
unfold merge. unfold In_graph. simpl.
apply VertexSet.remove_1. apply Vertex.eq_refl.
Qed.

Lemma merge_2 : forall x e g p q,
~Vertex.eq x (snd_ext e) ->
In_graph x g ->
In_graph x (merge e g p q).

Proof.
intros. unfold merge.
unfold In_graph. simpl. apply VertexSet.remove_2 with (x:=(snd_ext e)); auto.
Qed.

Lemma merge_3 : forall e e' g p q,
In_graph_edge e' g ->
interf_edge e' ->
In_graph_edge (redirect (snd_ext e) (fst_ext e) e') (merge e g p q).

Proof.
intros e e' g p q H0 H1. generalize I. intro H.
assert (EdgeSet.In (fst_ext e, snd_ext e, Some N0) (AE g)) as He.
destruct p. rewrite (edge_eq e) in H2.
generalize (AE_weights _ _ H2). intro. simpl in H3.
rewrite H3 in H2. assumption.
generalize (IE_weights _ _ H2). inversion q. congruence.
assert (VertexSet.In (snd_ext e) (adj_set (fst_ext e) (pmap g))) as Hee.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))).
assumption.
assert (EdgeSet.In (fst_ext e', snd_ext e', None) (IE g)) as He'.
destruct H0. generalize (AE_weights _ _ H0). intro H2. inversion H2. congruence.
rewrite (edge_eq e') in H0. generalize (IE_weights _ _ H0). intro. simpl in H2.
rewrite H2 in H0. assumption.
assert (VertexSet.In (snd_ext e') (adj_set (fst_ext e') (imap g))) as Hee'.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ None (sym_imap g))).
assumption.
assert (forall a b, VertexSet.In a (adj_set b (imap_merge e g)) ->
                    VertexSet.In b (adj_set a (imap_merge e g))) as Hsym.
apply sym_imap_merge_map; auto.

right.
unfold merge. unfold IE. simpl.
unfold redirect.
destruct (OTFacts.eq_dec (fst_ext e') (snd_ext e)).
rewrite H1. apply (proj2 (edgemap_to_edgeset_charac (imap_merge e g) _ _ None Hsym)).

unfold imap_merge.
unfold map_merge.
set (s := (VertexSet.union
              (VertexSet.remove (snd_ext e) (adj_set (fst_ext e) (imap g)))
              (VertexSet.remove (fst_ext e) (adj_set (snd_ext e) (imap g))))) in *.
set (m := imap g) in *.
set (f := (fun (y : VertexSet.elt) (m' : VertexMap.t VertexSet.t) =>
               VertexMap.add y
                 (VertexSet.add (fst_ext e)
                    (VertexSet.remove (snd_ext e) (adj_set y m))) m')) in *.
set (s' := VertexSet.remove (fst_ext e) (adj_set (snd_ext e) m)) in *.
unfold adj_set.
rewrite MapFacts.remove_neq_o.
rewrite MapFacts.add_eq_o.
unfold s.
apply VertexSet.union_3.
unfold s'.
apply VertexSet.remove_2.
intro.
elim (simple_graph g (fst_ext e) (snd_ext e)).
split.
rewrite H2. unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym r)).
fold (adj_set (fst_ext e') (imap g)).
assumption.
apply (sym_pmap g). assumption.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym r)).
fold (adj_set (fst_ext e') m).
assumption.
intuition.
apply (In_graph_edge_diff_ext _ _ p).

destruct (OTFacts.eq_dec (snd_ext e') (snd_ext e)).
rewrite H1.
apply (proj2 (edgemap_to_edgeset_charac (imap_merge e g) _ _ None Hsym)).
unfold imap_merge.
unfold map_merge.
set (s := (VertexSet.union
              (VertexSet.remove (snd_ext e) (adj_set (fst_ext e) (imap g)))
              (VertexSet.remove (fst_ext e) (adj_set (snd_ext e) (imap g))))) in *.
set (m := imap g) in *.
set (f := (fun (y : VertexSet.elt) (m' : VertexMap.t VertexSet.t) =>
               VertexMap.add y
                 (VertexSet.add (fst_ext e)
                    (VertexSet.remove (snd_ext e) (adj_set y m))) m')) in *.
set (s' := VertexSet.remove (fst_ext e) (adj_set (snd_ext e) m)) in *.
unfold adj_set.
rewrite MapFacts.remove_neq_o.
rewrite MapFacts.add_neq_o.
rewrite VertexSet.fold_1.
set (f' := fun a e => f e a).
generalize VertexSet.elements_1. intro HH.
generalize (HH s' (fst_ext e')). clear HH. intro HH.
induction (VertexSet.elements s'). simpl.
assert (InA Vertex.eq (fst_ext e') nil).
apply HH.
unfold s'. apply VertexSet.remove_2.
intro.
elim (simple_graph g (fst_ext e) (snd_ext e)).
split.
rewrite H2. unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym r)).
fold (adj_set (fst_ext e') (imap g)).
apply (sym_imap g). assumption.
apply (sym_pmap g). assumption.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym r)).
apply (sym_imap g). assumption.
inversion H2.

cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H2 (fst_ext e')). clear H2. intro H2. simpl. inversion H2;clear H2.
set (tmp := fold_left f' l m) in *.
unfold f' in H5. unfold f in H5.
destruct (Vertex.eq_dec (fst_ext e') a).
rewrite MapFacts.add_eq_o in H5. congruence. intuition.
rewrite MapFacts.add_neq_o in H5. rewrite <-H5 in IHl.
apply IHl.
intro. generalize (HH H2). clear HH. intro HH.
inversion HH; subst.
elim (n0 H6).
assumption.
auto.

set (tmp := fold_left f' l m) in *.
unfold f' in H4. unfold f in H4.
destruct (Vertex.eq_dec (fst_ext e') a).
rewrite MapFacts.add_eq_o in H4.
rewrite H5. inversion H4; subst; clear H4.
apply VertexSet.add_1. intuition. intuition.
rewrite MapFacts.add_neq_o in H4.
rewrite <-H4 in IHl.
rewrite H5. apply IHl.
intro. generalize (HH H2). clear HH. intro HH. inversion HH; subst.
elim (n0 H7).
assumption.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x y).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
apply VertexSet.eq_refl. intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H2. auto. auto.

intro.
elim (simple_graph g (fst_ext e) (snd_ext e)).
split.
rewrite H2. unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym r)).
fold (adj_set (fst_ext e') (imap g)).
apply (sym_imap g). assumption.
apply (sym_pmap g). assumption.

intuition.
rewrite (edge_eq e'). rewrite H1.
apply (proj2 (edgemap_to_edgeset_charac (imap_merge e g) _ _ None Hsym)).
unfold imap_merge.
unfold map_merge.
set (s := (VertexSet.union
              (VertexSet.remove (snd_ext e) (adj_set (fst_ext e) (imap g)))
              (VertexSet.remove (fst_ext e) (adj_set (snd_ext e) (imap g))))) in *.
set (m := imap g) in *.
set (f := (fun (y : VertexSet.elt) (m' : VertexMap.t VertexSet.t) =>
               VertexMap.add y
                 (VertexSet.add (fst_ext e)
                    (VertexSet.remove (snd_ext e) (adj_set y m))) m')) in *.
set (s' := VertexSet.remove (fst_ext e) (adj_set (snd_ext e) m)) in *.
unfold adj_set.
rewrite MapFacts.remove_neq_o.
destruct (Vertex.eq_dec (fst_ext e') (fst_ext e)).
rewrite MapFacts.add_eq_o.
unfold s.
apply VertexSet.union_2.
apply VertexSet.remove_2. intuition.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
assumption.
intuition.

rewrite MapFacts.add_neq_o.
rewrite VertexSet.fold_1.
set (f' := fun a e => f e a).
(*
generalize VertexSet.elements_1. intro HH.
generalize (HH s' (fst_ext e')). clear HH. intro HH.
*)
induction (VertexSet.elements s'). simpl. assumption.
cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H2 (fst_ext e')). clear H2. intro H2. simpl. inversion H2;clear H2.
set (tmp := fold_left f' l m) in *.
unfold f' in H5. unfold f in H5.
destruct (Vertex.eq_dec (fst_ext e') a).
rewrite MapFacts.add_eq_o in H5. congruence. intuition.
rewrite MapFacts.add_neq_o in H5. rewrite <-H5 in IHl.
apply IHl. auto.

set (tmp := fold_left f' l m) in *.
unfold f' in H4. unfold f in H4.
destruct (Vertex.eq_dec (fst_ext e') a).
rewrite MapFacts.add_eq_o in H4.
rewrite H5. inversion H4; subst; clear H4.
apply VertexSet.add_2. apply VertexSet.remove_2. intuition.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)). assumption.
intuition.

rewrite MapFacts.add_neq_o in H4.
rewrite <-H4 in IHl.
rewrite H5. apply IHl.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x y).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
apply VertexSet.eq_refl. intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H2. auto. auto.

auto.
intuition.
Qed.

Lemma merge_4 : forall e e' g p q,
In_graph_edge e' (merge e g p q) ->
exists a, In_graph_edge a g /\ weak_eq e' (redirect (snd_ext e) (fst_ext e) a)
              /\ same_type a e'.

Proof.
intros e e' g p q H0. generalize I. intro H.
generalize H0. intro Hin.
unfold merge in H0. destruct H0.
generalize (AE_weights _ _ H0). intro Hw.
unfold AE in H0. simpl in H0.
rewrite (edge_eq e') in H0. rewrite Hw in H0.
generalize (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap_merge_map _ _ q p)) H0).
clear H0. intro H0.
generalize (pmap_merge_sub _ _ _ _ H0). clear H0. intro H0.
unfold map_merge in H0.
set (s := (VertexSet.union
              (VertexSet.remove (snd_ext e) (adj_set (fst_ext e) (pmap g)))
              (VertexSet.remove (fst_ext e) (adj_set (snd_ext e) (pmap g))))) in *.
set (m := pmap g) in *.
set (f := (fun (y : VertexSet.elt) (m' : VertexMap.t VertexSet.t) =>
               VertexMap.add y
                 (VertexSet.add (fst_ext e)
                    (VertexSet.remove (snd_ext e) (adj_set y m))) m')) in *.
set (s' := VertexSet.remove (fst_ext e) (adj_set (snd_ext e) m)) in *.
unfold adj_set in H0.
destruct (Vertex.eq_dec (fst_ext e') (snd_ext e)).
rewrite MapFacts.remove_eq_o in H0.
elim (VertexSet.empty_1 H0). intuition.
rewrite MapFacts.remove_neq_o in H0.
destruct (Vertex.eq_dec (fst_ext e') (fst_ext e)).
rewrite MapFacts.add_eq_o in H0.
unfold s in H0.
destruct (VertexSet.union_1 H0).
generalize (VertexSet.remove_3 H1). clear H1. intro H1.
exists (fst_ext e', snd_ext e', Some N0). split.
left. unfold AE.
apply (proj2 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))).
unfold adj_set. rewrite (MapFacts.find_o _ e0). assumption.
unfold redirect. change_rewrite.
destruct (OTFacts.eq_dec (fst_ext e') (snd_ext e)).
elim (n r).
destruct (OTFacts.eq_dec (snd_ext e') (snd_ext e)).
elim (merge_1 e g p q).
rewrite <-r. apply (proj2 (In_graph_edge_in_ext _ _ Hin)).
split.
unfold weak_eq. change_rewrite.
left. split; auto.
unfold same_type. left. split. exists N0. auto. exists N0. auto.
unfold s' in H1.
generalize (VertexSet.remove_3 H1). intro H2.
exists (snd_ext e', snd_ext e, Some N0).
split.
left. unfold AE.
apply (proj2 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))).
apply (sym_pmap g). assumption.
unfold redirect. change_rewrite.
destruct (OTFacts.eq_dec (snd_ext e') (snd_ext e)).
unfold weak_eq. change_rewrite.
split.
left. split; auto.
unfold same_type. left. split; exists N0; auto.
destruct (OTFacts.eq_dec (snd_ext e) (snd_ext e)).
unfold weak_eq. change_rewrite.
split.
right. split; auto.
unfold same_type. left. split; exists N0; auto.
elim n1. intuition. intuition.
rewrite MapFacts.add_neq_o in H0.

rewrite VertexSet.fold_1 in H0.
set (f' := fun a e => f e a) in *.
generalize VertexSet.elements_2. intro HH.
generalize (HH s'). clear HH. intro HH.
induction (VertexSet.elements s'). simpl in H0.
case_eq (VertexMap.find (fst_ext e') m); intros. rewrite H1 in H0.
exists (fst_ext e', snd_ext e', Some N0).
split.
left. apply (proj2 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))).
unfold adj_set. fold m. rewrite H1. assumption.
unfold redirect. change_rewrite.
destruct (OTFacts.eq_dec (fst_ext e') (snd_ext e)).
elim (n r).
destruct (OTFacts.eq_dec (snd_ext e') (snd_ext e)).
elim (merge_1 e g p q).
rewrite <-r. apply (proj2 (In_graph_edge_in_ext _ _ Hin)).
unfold weak_eq. change_rewrite.
split.
left. split ; auto.
left. split; exists N0; auto.
rewrite H1 in H0. elim (VertexSet.empty_1 H0).
simpl in H0.
cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H1 (fst_ext e')). clear H1. intro H1. inversion H1; clear H1.
rewrite <-H3 in *. elim (VertexSet.empty_1 H0).
set (tmp := fold_left f' l m) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec (fst_ext e') a).
rewrite MapFacts.add_eq_o in H3. inversion H3; subst; clear H3.
rewrite <-H2 in H0.
rewrite H4 in H0. clear H4.
destruct (proj1 (Props.Dec.F.add_iff _ _ _ ) H0).
exists (fst_ext e', snd_ext e, Some N0).
split.
left. apply (proj2 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))).
apply (sym_pmap g).
assert (VertexSet.In (fst_ext e') s').
apply HH. left. auto.
unfold s' in H3. apply (VertexSet.remove_3 H3).
unfold redirect. change_rewrite.
destruct (OTFacts.eq_dec (fst_ext e') (snd_ext e)).
unfold weak_eq. change_rewrite.
split.
right. split; auto.
unfold same_type. left. split; exists N0; auto.
destruct (OTFacts.eq_dec (snd_ext e) (snd_ext e)).
unfold weak_eq. change_rewrite.
split.
left. split; auto.
left. split; exists N0; auto.
elim n2. intuition.
exists (fst_ext e', snd_ext e', Some N0).
split.
left.
apply (proj2 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))).
generalize (VertexSet.remove_3 H1). clear H1. intro H1.
unfold adj_set. rewrite (MapFacts.find_o _ e0). assumption.
unfold redirect. change_rewrite.
destruct (OTFacts.eq_dec (fst_ext e') (snd_ext e)).
elim (merge_1 e g p q).
rewrite <-r. apply (proj1 (In_graph_edge_in_ext _ _ Hin)).
destruct (OTFacts.eq_dec (snd_ext e') (snd_ext e)).
elim (merge_1 e g p q).
rewrite <-r. apply (proj2 (In_graph_edge_in_ext _ _ Hin)).
unfold weak_eq. change_rewrite.
split.
left. split; auto.
left. split; exists N0; auto.
intuition.
auto.

rewrite MapFacts.add_neq_o in H3. rewrite <-H3 in IHl.
apply IHl. rewrite <-H2 in H0. rewrite H4 in H0. auto.
intros. apply HH. auto.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x y).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H1. auto. auto.

auto.
auto.

generalize (IE_weights _ _ H0). intro Hw.
unfold IE in H0. simpl in H0.
rewrite (edge_eq e') in H0. rewrite Hw in H0.
generalize (proj1 (edgemap_to_edgeset_charac _ _ _ None (sym_imap_merge_map _ _ q p)) H0).
clear H0. intro H0.
unfold imap_merge in H0. unfold map_merge in H0.
set (s := (VertexSet.union
              (VertexSet.remove (snd_ext e) (adj_set (fst_ext e) (imap g)))
              (VertexSet.remove (fst_ext e) (adj_set (snd_ext e) (imap g))))) in *.
set (m := imap g) in *.
set (f := (fun (y : VertexSet.elt) (m' : VertexMap.t VertexSet.t) =>
               VertexMap.add y
                 (VertexSet.add (fst_ext e)
                    (VertexSet.remove (snd_ext e) (adj_set y m))) m')) in *.
set (s' := VertexSet.remove (fst_ext e) (adj_set (snd_ext e) m)) in *.
unfold adj_set in H0.
destruct (Vertex.eq_dec (fst_ext e') (snd_ext e)).
rewrite MapFacts.remove_eq_o in H0.
elim (VertexSet.empty_1 H0). intuition.
rewrite MapFacts.remove_neq_o in H0.
destruct (Vertex.eq_dec (fst_ext e') (fst_ext e)).
rewrite MapFacts.add_eq_o in H0.
unfold s in H0.
destruct (VertexSet.union_1 H0).
generalize (VertexSet.remove_3 H1). clear H1. intro H1.
exists (fst_ext e', snd_ext e', None). split.
right. unfold IE.
apply (proj2 (edgemap_to_edgeset_charac _ _ _ None (sym_imap g))).
unfold adj_set. rewrite (MapFacts.find_o _ e0). assumption.
unfold redirect. change_rewrite.
destruct (OTFacts.eq_dec (fst_ext e') (snd_ext e)).
elim (n r).
destruct (OTFacts.eq_dec (snd_ext e') (snd_ext e)).
elim (merge_1 e g p q).
rewrite <-r. apply (proj2 (In_graph_edge_in_ext _ _ Hin)).
unfold weak_eq. change_rewrite.
split. left; split; auto.
right; split; unfold interf_edge; simpl; auto.
unfold s' in H1.
generalize (VertexSet.remove_3 H1). intro H2.
exists (snd_ext e', snd_ext e, None).
split.
right. unfold IE.
apply (proj2 (edgemap_to_edgeset_charac _ _ _ None (sym_imap g))).
apply (sym_imap g). assumption.
unfold redirect. change_rewrite.
destruct (OTFacts.eq_dec (snd_ext e') (snd_ext e)).
unfold weak_eq. change_rewrite.
split.
left. split; auto.
right. unfold interf_edge;split; simpl; auto.
destruct (OTFacts.eq_dec (snd_ext e) (snd_ext e)).
unfold weak_eq. change_rewrite.
split.
right. split; auto.
right. unfold interf_edge; split; simpl; auto.
elim n1. intuition.
intuition.
rewrite MapFacts.add_neq_o in H0.

rewrite VertexSet.fold_1 in H0.
set (f' := fun a e => f e a) in *.
generalize VertexSet.elements_2. intro HH.
generalize (HH s'). clear HH. intro HH.
induction (VertexSet.elements s'). simpl in H0.
case_eq (VertexMap.find (fst_ext e') m); intros. rewrite H1 in H0.
exists (fst_ext e', snd_ext e', None).
split.
right. apply (proj2 (edgemap_to_edgeset_charac _ _ _ None (sym_imap g))).
unfold adj_set. fold m. rewrite H1. assumption.
unfold redirect. change_rewrite.
destruct (OTFacts.eq_dec (fst_ext e') (snd_ext e)).
elim (n r).
destruct (OTFacts.eq_dec (snd_ext e') (snd_ext e)).
elim (merge_1 e g p q).
rewrite <-r. apply (proj2 (In_graph_edge_in_ext _ _ Hin)).
unfold weak_eq. change_rewrite.
split.
left. split; auto.
right. unfold interf_edge; split; simpl; auto.
rewrite H1 in H0. elim (VertexSet.empty_1 H0).
simpl in H0.
cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H1 (fst_ext e')). clear H1. intro H1. inversion H1; clear H1.
rewrite <-H3 in *. elim (VertexSet.empty_1 H0).
set (tmp := fold_left f' l m) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec (fst_ext e') a).
rewrite MapFacts.add_eq_o in H3. inversion H3; subst; clear H3.
rewrite <-H2 in H0.
rewrite H4 in H0. clear H4.
destruct (proj1 (Props.Dec.F.add_iff _ _ _ ) H0).
exists (fst_ext e', snd_ext e, None).
split.
right. apply (proj2 (edgemap_to_edgeset_charac _ _ _ None (sym_imap g))).
apply (sym_imap g).
assert (VertexSet.In (fst_ext e') s').
apply HH. left. auto.
unfold s' in H3. apply (VertexSet.remove_3 H3).
unfold redirect. change_rewrite.
destruct (OTFacts.eq_dec (fst_ext e') (snd_ext e)).
unfold weak_eq. change_rewrite.
split.
right. split; auto.
right. unfold interf_edge; split; simpl; auto.
destruct (OTFacts.eq_dec (snd_ext e) (snd_ext e)).
unfold weak_eq. change_rewrite.
split.
left. split; auto.
right. unfold interf_edge; split; simpl; auto.
elim n2. intuition.
exists (fst_ext e', snd_ext e', None).
split.
right. apply (proj2 (edgemap_to_edgeset_charac _ _ _ None (sym_imap g))).
generalize (VertexSet.remove_3 H1). clear H1. intro H1.
unfold adj_set. rewrite (MapFacts.find_o _ e0). assumption.
unfold redirect. change_rewrite.
destruct (OTFacts.eq_dec (fst_ext e') (snd_ext e)).
elim (merge_1 e g p q).
rewrite <-r. apply (proj1 (In_graph_edge_in_ext _ _ Hin)).
destruct (OTFacts.eq_dec (snd_ext e') (snd_ext e)).
elim (merge_1 e g p q).
rewrite <-r. apply (proj2 (In_graph_edge_in_ext _ _ Hin)).
unfold weak_eq. change_rewrite.
split.
left. split; auto.
right. unfold interf_edge; split; simpl; auto.
intuition.

rewrite MapFacts.add_neq_o in H3. rewrite <-H3 in IHl.
apply IHl. rewrite <-H2 in H0. rewrite H4 in H0. auto.
intros. apply HH. auto.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x y).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
apply VertexSet.eq_refl.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H1. auto. auto.

auto.
auto.
Qed.

Lemma resolve_conflicts_map_5 : forall x y e g,
aff_edge e ->
In_graph_edge e g ->
VertexSet.In x (adj_set y (map_merge e (pmap g))) ->
~VertexSet.In x (adj_set y (imap_merge e g)) ->
VertexSet.In x (adj_set y (resolve_conflicts (fst_ext e) (map_merge e (pmap g))
                                   (adj_set (fst_ext e) (map_merge e (pmap g)))
                                   (adj_set (fst_ext e) (imap_merge e g)))).

Proof.
intros x y e g p q H H0.
unfold resolve_conflicts.
set (f := (fun (x0 : VertexSet.elt) (m : VertexMap.t VertexSet.t) =>
            VertexMap.add x0
              (VertexSet.remove (fst_ext e)
                 (adj_set x0 (map_merge e (pmap g)))) m)) in *.
set (m := map_merge e (pmap g)) in *.
set (s' :=  (VertexSet.diff (adj_set (fst_ext e) m)
           (adj_set (fst_ext e) (imap_merge e g)))) in *.
set (s :=  (VertexSet.inter (adj_set (fst_ext e) m)
              (adj_set (fst_ext e) (imap_merge e g)))) in *.
rewrite VertexSet.fold_1.
set (f' := fun a e => f e a) in *.
generalize VertexSet.elements_1. intro.
generalize (H1 s y). clear H1. intro HH.
generalize VertexSet.elements_2. intro.
generalize (H1 s y). clear H1. intro HHH.
induction (VertexSet.elements s). simpl.
destruct (Vertex.eq_dec y (fst_ext e)).
unfold adj_set. rewrite (MapFacts.find_o _ e0).
rewrite MapFacts.add_eq_o. 
apply VertexSet.diff_3.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)). assumption.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)). assumption.
intuition.
unfold adj_set. rewrite MapFacts.add_neq_o. assumption.
auto.

cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)).
intro. generalize (H1 y). clear H1. intro H1. simpl. inversion H1; clear H1.
set (tmp := fold_left f' l m) in *.
unfold f' in H4. unfold f in H4.
destruct (Vertex.eq_dec y a).
rewrite MapFacts.add_eq_o in H4. congruence. intuition.
destruct (Vertex.eq_dec y (fst_ext e)). unfold adj_set.
rewrite MapFacts.add_eq_o.
unfold adj_set in IHl.
rewrite MapFacts.add_eq_o in IHl.
apply IHl. intro.
generalize (HH H1). intro.
inversion H2; subst.
elim (n H6).
auto.
intro. apply HHH. right. auto.
intuition.
intuition.

rewrite MapFacts.add_neq_o in H4.
unfold adj_set in IHl. rewrite MapFacts.add_neq_o in IHl.
rewrite <-H4 in IHl.
assert (VertexSet.In x VertexSet.empty).
apply IHl. intro.
generalize (HH H1). intro.
inversion H2; subst.
elim (n H6).
auto.
intro. apply HHH. right. auto.
elim (VertexSet.empty_1 H1).
auto.
auto.
auto.

set (tmp := fold_left f' l m) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec y a).
rewrite MapFacts.add_eq_o in H3.
unfold adj_set. destruct (Vertex.eq_dec y (fst_ext e)).
rewrite MapFacts.add_eq_o.
apply VertexSet.diff_3.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)). assumption.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)). assumption.
intuition.

rewrite MapFacts.add_neq_o. rewrite <-H2. rewrite H4.
inversion H3; subst; clear H3.
apply VertexSet.remove_2.

intro H5.
assert (VertexSet.In y s).
apply HHH. left. auto.
generalize (VertexSet.inter_2 H1). intro.
unfold adj_set in H3. rewrite (MapFacts.find_o _ H5) in H3.
generalize (sym_imap_merge_map e g p q _ _ H3). intro.
elim H0. assumption.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
auto.
auto.
intuition.

rewrite MapFacts.add_neq_o in H3.
destruct (Vertex.eq_dec y (fst_ext e)).
unfold adj_set in IHl.
rewrite MapFacts.add_eq_o in IHl.
unfold adj_set. rewrite MapFacts.add_eq_o.
apply IHl.

intro. generalize (HH H1). intro.
inversion H5; subst.
elim (n H7).
auto.

intro. apply HHH. right. auto.
intuition.
intuition.

unfold adj_set in IHl. rewrite MapFacts.add_neq_o in IHl.
unfold adj_set. rewrite MapFacts.add_neq_o.
rewrite <-H2.
rewrite <-H3 in IHl.
rewrite H4.
apply IHl.

intro. generalize (HH H1). intro.
inversion H5; subst.
elim (n H7).
auto.

intro. apply HHH. right. auto.
auto.
auto.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
apply VertexSet.eq_refl. intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 y0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H1. auto. auto.
Qed.

Lemma merge_3_aux : forall e e' g,
aff_edge e ->
In_graph_edge e g ->
In_graph_edge e' g ->
aff_edge e' ->
~Edge.eq e e' ->
VertexSet.In (snd_ext (redirect (snd_ext e) (fst_ext e) e'))
             (adj_set (fst_ext (redirect (snd_ext e) (fst_ext e) e')) (map_merge e (pmap g))).

Proof.
intros e e' g q p H0 H1 Hdiff. generalize I. intro H.
assert (get_weight e = Some N0) as Hw.
destruct p. apply (AE_weights _ _ H2).
generalize (IE_weights _ _ H2). inversion q. congruence.
assert (get_weight e' = Some N0) as Hw'.
destruct H0. apply (AE_weights _ _ H0).
generalize (IE_weights _ _ H0). inversion H1. congruence.
assert (EdgeSet.In (fst_ext e, snd_ext e, Some N0) (AE g)) as He.
destruct p. rewrite (edge_eq e) in H2.
generalize (AE_weights _ _ H2). intro. simpl in H3.
rewrite H3 in H2. assumption.
generalize (IE_weights _ _ H2). inversion q. congruence.
assert (VertexSet.In (snd_ext e) (adj_set (fst_ext e) (pmap g))) as Hee.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))).
assumption.
assert (EdgeSet.In (fst_ext e', snd_ext e', Some N0) (AE g)) as He'.
destruct H0.  rewrite (edge_eq e') in H0.
generalize (AE_weights _ _ H0). intro. simpl in H2.
rewrite H2 in H0. assumption.
generalize (IE_weights _ _ H0). intro H2. inversion H1. congruence.
assert (VertexSet.In (snd_ext e') (adj_set (fst_ext e') (pmap g))) as Hee'.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))).
assumption.
assert (forall a b, VertexSet.In a (adj_set b (map_merge e (pmap g))) ->
                    VertexSet.In b (adj_set a (map_merge e (pmap g)))) as Hsym.
intros; apply sym_map_merge_pmap; auto.

unfold redirect.
destruct (OTFacts.eq_dec (fst_ext e') (snd_ext e)).
unfold map_merge.
set (s := (VertexSet.union
              (VertexSet.remove (snd_ext e) (adj_set (fst_ext e) (pmap g)))
              (VertexSet.remove (fst_ext e) (adj_set (snd_ext e) (pmap g))))) in *.
set (m := pmap g) in *.
set (f := (fun (y : VertexSet.elt) (m' : VertexMap.t VertexSet.t) =>
               VertexMap.add y
                 (VertexSet.add (fst_ext e)
                    (VertexSet.remove (snd_ext e) (adj_set y m))) m')) in *.
set (s' := VertexSet.remove (fst_ext e) (adj_set (snd_ext e) m)) in *.
unfold adj_set.
rewrite MapFacts.remove_neq_o.
rewrite MapFacts.add_eq_o.
unfold s.
apply VertexSet.union_3.
unfold s'.
apply VertexSet.remove_2.
intro. change_rewrite.
elim Hdiff.
rewrite (edge_eq e). rewrite edge_comm. apply eq_ordered_eq.
rewrite (edge_eq e'). unfold E.eq; change_rewrite; simpl; intuition.
rewrite Hw. rewrite Hw'. apply OptionN_as_OT.eq_refl.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym r)).
fold (adj_set (fst_ext e') m).
assumption. change_rewrite. intuition.
change_rewrite.
apply (In_graph_edge_diff_ext _ _ p).

destruct (OTFacts.eq_dec (snd_ext e') (snd_ext e)); change_rewrite.
unfold map_merge.
set (s := (VertexSet.union
              (VertexSet.remove (snd_ext e) (adj_set (fst_ext e) (pmap g)))
              (VertexSet.remove (fst_ext e) (adj_set (snd_ext e) (pmap g))))) in *.
set (m := pmap g) in *.
set (f := (fun (y : VertexSet.elt) (m' : VertexMap.t VertexSet.t) =>
               VertexMap.add y
                 (VertexSet.add (fst_ext e)
                    (VertexSet.remove (snd_ext e) (adj_set y m))) m')) in *.
set (s' := VertexSet.remove (fst_ext e) (adj_set (snd_ext e) m)) in *.
unfold adj_set.
rewrite MapFacts.remove_neq_o.
rewrite MapFacts.add_neq_o.
rewrite VertexSet.fold_1.
set (f' := fun a e => f e a).
generalize VertexSet.elements_1. intro HH.
generalize (HH s' (fst_ext e')). clear HH. intro HH.
induction (VertexSet.elements s'). simpl.
assert (InA Vertex.eq (fst_ext e') nil).
apply HH.
unfold s'. apply VertexSet.remove_2.
intro. elim Hdiff.
apply eq_ordered_eq.
rewrite (edge_eq e). rewrite (edge_eq e'). 
unfold E.eq; change_rewrite; simpl; intuition.
rewrite Hw. rewrite Hw'. apply OptionN_as_OT.eq_refl.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym r)).
apply (sym_pmap g). assumption.
inversion H2.

cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H2 (fst_ext e')). clear H2. intro H2. simpl. inversion H2;clear H2.
set (tmp := fold_left f' l m) in *.
unfold f' in H5. unfold f in H5.
destruct (Vertex.eq_dec (fst_ext e') a).
rewrite MapFacts.add_eq_o in H5. congruence. intuition.
rewrite MapFacts.add_neq_o in H5. rewrite <-H5 in IHl.
apply IHl.
intro. generalize (HH H2). clear HH. intro HH.
inversion HH; subst.
elim (n0 H6).
assumption.
auto.

set (tmp := fold_left f' l m) in *.
unfold f' in H4. unfold f in H4.
destruct (Vertex.eq_dec (fst_ext e') a).
rewrite MapFacts.add_eq_o in H4.
rewrite H5. inversion H4; subst; clear H4.
apply VertexSet.add_1. intuition. intuition.
rewrite MapFacts.add_neq_o in H4.
rewrite <-H4 in IHl.
rewrite H5. apply IHl.
intro. generalize (HH H2). clear HH. intro HH. inversion HH; subst.
elim (n0 H7).
assumption.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x y).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
apply VertexSet.eq_refl. intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H2. auto. auto.

intro. elim Hdiff.
apply eq_ordered_eq.
rewrite (edge_eq e). rewrite (edge_eq e').
unfold E.eq; change_rewrite; simpl; intuition.
rewrite Hw. rewrite Hw'. apply OptionN_as_OT.eq_refl.

intuition.
unfold map_merge.
set (s := (VertexSet.union
              (VertexSet.remove (snd_ext e) (adj_set (fst_ext e) (pmap g)))
              (VertexSet.remove (fst_ext e) (adj_set (snd_ext e) (pmap g))))) in *.
set (m := pmap g) in *.
set (f := (fun (y : VertexSet.elt) (m' : VertexMap.t VertexSet.t) =>
               VertexMap.add y
                 (VertexSet.add (fst_ext e)
                    (VertexSet.remove (snd_ext e) (adj_set y m))) m')) in *.
set (s' := VertexSet.remove (fst_ext e) (adj_set (snd_ext e) m)) in *.
unfold adj_set.
rewrite MapFacts.remove_neq_o.
destruct (Vertex.eq_dec (fst_ext e') (fst_ext e)).
rewrite MapFacts.add_eq_o.
unfold s.
apply VertexSet.union_2.
apply VertexSet.remove_2. intuition.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
assumption.
intuition.

rewrite MapFacts.add_neq_o.
rewrite VertexSet.fold_1.
set (f' := fun a e => f e a).
(*
generalize VertexSet.elements_1. intro HH.
generalize (HH s' (fst_ext e')). clear HH. intro HH.
*)
induction (VertexSet.elements s'). simpl. assumption.
cut (EqualSetMap (fold_left f' (a :: l) m) (f' (fold_left f' l m) a)). intro.
generalize (H2 (fst_ext e')). clear H2. intro H2. simpl. inversion H2;clear H2.
set (tmp := fold_left f' l m) in *.
unfold f' in H5. unfold f in H5.
destruct (Vertex.eq_dec (fst_ext e') a).
rewrite MapFacts.add_eq_o in H5. congruence. intuition.
rewrite MapFacts.add_neq_o in H5. rewrite <-H5 in IHl.
apply IHl. auto.

set (tmp := fold_left f' l m) in *.
unfold f' in H4. unfold f in H4.
destruct (Vertex.eq_dec (fst_ext e') a).
rewrite MapFacts.add_eq_o in H4.
rewrite H5. inversion H4; subst; clear H4.
apply VertexSet.add_2. apply VertexSet.remove_2. intuition.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)). assumption.
intuition.

rewrite MapFacts.add_neq_o in H4.
rewrite <-H4 in IHl.
rewrite H5. apply IHl.
auto.

apply fold_left_assoc_map.
unfold EqualSetMap. unfold f'. unfold f.
intros.
destruct (Vertex.eq_dec x z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x y).
rewrite MapFacts.add_eq_o.
constructor.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_sym e1)).
rewrite (MapFacts.find_o _ (Vertex.eq_sym e0)).
apply VertexSet.eq_refl. intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x s0); constructor; apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f'. unfold f.
destruct (Vertex.eq_dec x a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H2. auto. auto.

auto.
intuition.
Qed.

Lemma merge_5 : forall e e' g p q,
In_graph_edge e' g ->
~Edge.eq e e' ->
aff_edge e' ->
~Interfere (fst_ext (redirect (snd_ext e) (fst_ext e) e'))
           (snd_ext (redirect (snd_ext e) (fst_ext e) e')) 
           (merge e g p q) ->
Prefere (fst_ext (redirect (snd_ext e) (fst_ext e) e'))
        (snd_ext (redirect (snd_ext e) (fst_ext e) e'))
        (merge e g p q).

Proof.
intros e e' g p q H0 H1 H2 H3. generalize I. intro H.
unfold Prefere. exists N0. left.
unfold merge. unfold AE. simpl.
apply (proj2 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap_merge_map e g q p))).
apply resolve_conflicts_map_5.
assumption.
assumption.
apply merge_3_aux; assumption.
intro. elim H3. unfold Interfere. right. unfold merge.
unfold IE. simpl.
apply (proj2 (edgemap_to_edgeset_charac _ _ _ None (sym_imap_merge_map e g q p))).
assumption.
Qed.
(*
unfold change.
destruct (OTFacts.eq_dec (fst_ext e') (snd_ext e)). change_rewrite.
apply VertexSet.remove_2.
apply (In_graph_edge_diff_ext e g p).
apply (proj1 (In_graph_edge_in_ext _ _ p)).
destruct (OTFacts.eq_dec (snd_ext e') (snd_ext e)). change_rewrite.
apply VertexSet.remove_2.
intro. elim (In_graph_edge_diff_ext e' g H0).
apply Vertex.eq_trans with (y := snd_ext e); auto.
apply (proj1 (In_graph_edge_in_ext _ _ H0)).
apply VertexSet.remove_2.
auto.
apply (proj1 (In_graph_edge_in_ext _ _ H0)).
Qed.
*)

Lemma precolored_merge2 : forall x e g p q,
(VertexSet.In x (VertexSet.remove (snd_ext e) (precolored g)) <->
 VertexSet.In x (precolored (merge e g p q))).

Proof.
intros x e g HH q. split; intros.
unfold merge.
unfold precolored. simpl. unfold is_precolored. simpl.
apply VertexSet.filter_3.
unfold compat_bool;intros.
rewrite (mreg_ext _ _ H0). auto.
apply VertexSet.remove_2.
intro H1. elim (VertexSet.remove_1 H1 H).
apply (VertexSet.filter_1 (compat_bool_is_precolored _) (VertexSet.remove_3 H)).
generalize (VertexSet.filter_2 (compat_bool_is_precolored _) (VertexSet.remove_3 H)). intro H0.
assumption.

unfold precolored, is_precolored in *. unfold merge in H. simpl in H.
apply VertexSet.remove_2. intro.
generalize (VertexSet.filter_1 (compat_bool_is_precolored (merge e g HH q)) H). intro.
elim (VertexSet.remove_1 H0 H1).
apply VertexSet.filter_3.
unfold compat_bool. apply mreg_ext.
generalize (VertexSet.filter_1 (compat_bool_is_precolored (merge e g HH q)) H). intros.
apply (VertexSet.remove_3 H0).
apply (VertexSet.filter_2 (compat_bool_is_precolored (merge e g HH q)) H).
Qed.

(* spec of delete_preference_edges *)
Lemma delete_preference_edges_prec : forall r g Hin,
VertexSet.Equal (precolored (delete_preference_edges r g Hin)) (precolored g).

Proof.
intros.
unfold delete_preference_edges.
unfold precolored. simpl.
unfold is_precolored. simpl.
apply VertexSet.eq_refl.
Qed.

Lemma delete_preference_edges_1 : forall e r g Hin,
In_graph_edge e (delete_preference_edges r g Hin) -> In_graph_edge e g.

Proof.
intros.
unfold delete_preference_edges in H.
destruct H;[left; generalize (AE_weights _ _ H); unfold AE in *|
            right; generalize (IE_weights _ _ H); unfold IE in *]; simpl in H; intros.
rewrite (edge_eq e) in H.
rewrite H0 in H. generalize (proj1 (edgemap_to_edgeset_charac _ _ _ _(sym_pmap_delete_preferences r g)) H). intro.
rewrite (edge_eq e).
rewrite H0. apply (proj2 (edgemap_to_edgeset_charac _ _ _ _ (sym_pmap g))).
apply (delete_preference_sub _ _ _ _ H1).
assumption.
Qed.

Lemma IE_delete_preference_eq  : forall x g H,
EdgeSet.Equal (IE g) (IE (delete_preference_edges x g H)).

Proof.
intros.
unfold delete_preference_edges.
destruct (In_graph_dec x g).
unfold IE. simpl. apply EdgeSet.eq_refl.
apply EdgeSet.eq_refl.
Qed.

Lemma delete_preference_edges_2 : forall e r g Hin,
In_graph_edge e g ->
~incident e r ->
In_graph_edge e (delete_preference_edges r g Hin).

Proof.
intros.
destruct H;[left|right].
generalize (AE_weights _ _ H). intro Hw.
unfold AE in *.
rewrite (edge_eq e). rewrite Hw.
unfold delete_preference_edges.
apply (proj2 (edgemap_to_edgeset_charac _ _ _ _ (sym_pmap_delete_preferences r g))).
unfold pmap_delete_preferences.
rewrite VertexSet.fold_1.
induction (VertexSet.elements (adj_set r (pmap g))). simpl.
unfold adj_set. rewrite InterfFacts.add_neq_o.
rewrite (edge_eq e) in H. rewrite Hw in H.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ _ (sym_pmap g)) H).
intro H1. elim H0. left. auto.

cut (EqualSetMap
       (fold_left
          (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
           VertexMap.add e (VertexSet.remove r (adj_set e (pmap g))) a) (a :: l)
          (VertexMap.add r VertexSet.empty (pmap g)))
       (VertexMap.add a
          (VertexSet.remove r
             (adj_set a (pmap g)))
          (fold_left
             (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
              VertexMap.add e (VertexSet.remove r (adj_set e (pmap g))) a) l
             (VertexMap.add r VertexSet.empty (pmap g))))). intro.
unfold EqualSetMap in H1. generalize (H1 (fst_ext e)). clear H1. intro H1.
inversion H1. simpl. unfold adj_set in *. rewrite <-H3.
destruct (Vertex.eq_dec (fst_ext e) a).
rewrite InterfFacts.add_eq_o in H4. inversion H4.
intuition.
rewrite InterfFacts.add_neq_o in H4. rewrite <-H4 in *.
elim (VertexSet.empty_1 IHl).
auto.
simpl. unfold adj_set in *. rewrite <-H2.
rewrite H4. clear H1. clear H2. clear H4.
destruct (Vertex.eq_dec (fst_ext e) a).
rewrite InterfFacts.add_eq_o in H3.
inversion H3. clear H2.
apply VertexSet.remove_2.
intro. elim H0. right. auto.
clear H3.
rewrite (edge_eq e) in H. rewrite Hw in H.
rewrite (InterfFacts.find_o _ (Vertex.eq_sym e0)).
apply (proj1 (edgemap_to_edgeset_charac _ _ _ _(sym_pmap g)) H).
intuition.
rewrite (InterfFacts.add_neq_o) in H3.
case_eq (VertexMap.find (elt:=VertexSet.t) (fst_ext e)
            (fold_left
               (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
                VertexMap.add e
                  (VertexSet.remove r
                     match VertexMap.find (elt:=VertexSet.t) e (pmap g) with
                     | Some x => x
                     | None => VertexSet.empty
                     end) a) l (VertexMap.add r VertexSet.empty (pmap g))));
intros; rewrite H1 in *.
inversion H3. assumption.
inversion H3.
auto.

apply fold_left_assoc_map.
intros.
unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x z).
rewrite InterfFacts.add_eq_o.
destruct (Vertex.eq_dec x y).
rewrite InterfFacts.add_eq_o.
constructor.
generalize (Vertex.eq_trans (Vertex.eq_sym e0) e1). intro HHH.
unfold adj_set.
rewrite (InterfFacts.find_o _ HHH). apply VertexSet.eq_refl.
intuition.

rewrite InterfFacts.add_neq_o.
rewrite InterfFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
auto.
intuition.

rewrite InterfFacts.add_neq_o.
destruct (Vertex.eq_dec x y).
rewrite InterfFacts.add_eq_o.
rewrite InterfFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.

intros.
unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x y).
rewrite InterfFacts.add_eq_o.
rewrite InterfFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite InterfFacts.add_neq_o.
rewrite InterfFacts.add_neq_o.
rewrite InterfFacts.add_neq_o.
apply EqualSetMap_refl.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x a0).
rewrite InterfFacts.add_eq_o.
rewrite InterfFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
intuition.
intuition.
rewrite InterfFacts.add_neq_o.
rewrite InterfFacts.add_neq_o.
apply (H1 x).
auto.
auto.

rewrite <-IE_delete_preference_eq. auto.
Qed.

Lemma V_delete_preference_eq : forall x g Hin,
VertexSet.Equal (V g) (V (delete_preference_edges x g Hin)).

Proof.
intros.
unfold delete_preference_edges.
destruct (In_graph_dec x g); simpl;  apply VertexSet.eq_refl.
Qed.

Lemma in_delete_preference_not_incident : forall e r g Hdep,
EdgeSet.In e (AE (delete_preference_edges r g Hdep)) -> ~incident e r.

Proof.
intros.
generalize (AE_weights _ _ H). intro Hw.
generalize (proj1 (In_graph_aff_edge_in_AE _ _) H). intro Hin.
unfold AE in H.
rewrite (edge_eq e) in H. rewrite Hw in H.
unfold delete_preference_edges in H.
generalize (proj1 (edgemap_to_edgeset_charac _ _ _ _(sym_pmap_delete_preferences r g)) H). clear H. intro H.
unfold pmap_delete_preferences in H.
rewrite VertexSet.fold_1 in H.
generalize VertexSet.elements_1. intro HH.
generalize (HH (adj_set r (pmap g)) (fst_ext e)). clear HH. intro HH.
generalize VertexSet.elements_2. intro HH1.
generalize (HH1 (adj_set r (pmap g))). clear HH1. intro HH1.

assert (forall z, In z (VertexSet.elements (adj_set r (pmap g))) -> ~Vertex.eq r z) as Hneq.
clear H HH Hin Hw Hdep.
intros. intro H0.
induction (VertexSet.elements (adj_set r (pmap g))). inversion H.
simpl in H. destruct H. subst.
assert (VertexSet.In r (adj_set r (pmap g))).
apply HH1. left. auto.
elim (not_eq_extremities g r r).
right. assumption.
auto.
apply IHl.
intros. apply HH1. auto.
assumption.

induction (VertexSet.elements (adj_set r (pmap g))). simpl in H.
unfold adj_set in H.
destruct (Vertex.eq_dec (fst_ext e) r).
rewrite InterfFacts.add_eq_o in H.
elim (VertexSet.empty_1 H). intuition.
rewrite InterfFacts.add_neq_o in H.
destruct (Vertex.eq_dec (snd_ext e) r).
assert (InA Vertex.eq (fst_ext e) nil).
apply HH.
apply (proj1 (edgemap_to_edgeset_charac (pmap g) r (fst_ext e) (Some N0) (sym_pmap g))).
assert (eq (r,fst_ext e, Some N0) e).
rewrite edge_comm.
apply eq_ordered_eq.
unfold E.eq; simpl; intuition. apply Regs.eq_refl.
rewrite <-Hw. apply OptionN_as_OT.eq_refl.
rewrite H0.
destruct Hin.
generalize (delete_preference_edges_1 e r g Hdep H2). clear H2. intro H2.
destruct H2.
unfold AE in H2. assumption.
generalize (IE_weights _ _ H2). intro Hw'. rewrite Hw' in Hw. inversion Hw.
inversion H0.
intro H0. destruct H0.
elim n. auto.
elim n0. auto.
auto.

set (f := (fun (a : VertexMap.t VertexSet.t) (e : VertexSet.elt) =>
               VertexMap.add e (VertexSet.remove r (adj_set e (pmap g))) a)) in *.
set (s := VertexMap.add r VertexSet.empty (pmap g)) in *.

assert (EqualSetMap (fold_left f (a :: l) s) (f (fold_left f l s) a)).
apply fold_left_assoc_map.

unfold f. unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x y).
rewrite MapFacts.add_eq_o.
constructor.
apply Props.Equal_remove.
unfold adj_set.
rewrite (MapFacts.find_o _ (Vertex.eq_trans (Vertex.eq_sym e0) e1)).
apply VertexSet.eq_refl. intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x s0); constructor.
apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.

unfold f. unfold EqualSetMap. intros.
destruct (Vertex.eq_dec x a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
apply VertexSet.eq_refl.
intuition.
intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H0.
auto.
auto.

generalize (H0 (fst_ext e)). clear H0. intro H0.
simpl in H. unfold adj_set in H.
inversion H0. subst.
rewrite <-H2 in H.
elim (VertexSet.empty_1 H).
rewrite <-H1 in H.
set (tmp := fold_left f l s) in *.
unfold f in H2.
destruct (Vertex.eq_dec (fst_ext e) a).
rewrite MapFacts.add_eq_o in H2.
intro.
inversion H2. subst. clear H2.
rewrite H3 in H.
destruct H4.

elim (Hneq a).
left. auto.
apply (Vertex.eq_trans H2 e0).
elim (VertexSet.remove_1 H2 H).
intuition.

rewrite MapFacts.add_neq_o in H2.
inversion H2. subst. clear H2.
apply IHl.
clear IHl.
unfold adj_set. rewrite <-H5.
rewrite <-H3. assumption.
intro.
assert (InA Vertex.eq (fst_ext e) (a :: l)).
apply HH. assumption.
inversion H4; subst.
elim (n H7).
assumption.
intros. apply HH1. auto.
intros. apply Hneq. right. auto.
auto.
Qed.

Add Morphism In_graph_edge : In_graph_edge_m.

Proof.
unfold In_graph_edge;intros x y H g.
fold (eq x y) in H.
split;intro H0;[rewrite <-H|rewrite H];assumption.
Qed.

(* There cannot exist both an interference and 
   a preference between two vertices *)
Lemma interf_pref_conflict : forall x y g,
Prefere x y g /\ Interfere x y g -> False.

Proof.
intros.
unfold Prefere in H. unfold Interfere in H.
destruct H.
apply (simple_graph g x y).
split.
destruct H0.
generalize (proj1 (In_graph_aff_edge_in_AE _ _) H0). intro H1.
destruct H1 as [H1 _].
unfold aff_edge in H1.
destruct H1. inversion H1.
unfold IE in H0.
rewrite edge_comm in H0. apply (proj1 (edgemap_to_edgeset_charac _ _ _ _ (sym_imap g)) H0).
destruct H. destruct H. generalize (AE_weights _ _ H). simpl. intro.
rewrite H1 in H.
rewrite edge_comm in H. unfold AE in H. apply (proj1 (edgemap_to_edgeset_charac _ _ _ _(sym_pmap g)) H).
generalize (proj1 (In_graph_interf_edge_in_IE _ _) H). intro H1.
destruct H1 as [H1 _].
unfold interf_edge in H1. inversion H1.
Qed.

Lemma is_simple_graph : forall e e' g,
In_graph_edge e g ->
In_graph_edge e' g ->
weak_eq e e' ->
eq e e'.

Proof.
intros.
unfold weak_eq in H1.
destruct H; destruct H0.
generalize (AE_weights _ _ H); intros.
generalize (AE_weights _ _ H0); intros.
destruct H1; destruct H1.
rewrite (edge_eq e). rewrite (edge_eq e'). rewrite H2. rewrite H3. Eq_eq.
rewrite (edge_eq e). rewrite (edge_eq e'). rewrite H2. rewrite H3. Eq_comm_eq.
elim (interf_pref_conflict (fst_ext e') (snd_ext e') g).
unfold Prefere, Interfere; split.
destruct H1; destruct H1. exists N0.
rewrite <-(AE_weights _ _ H).
assert (eq (fst_ext e', snd_ext e', get_weight e) (fst_ext e, snd_ext e, get_weight e)) by Eq_eq.
rewrite H3. rewrite <-(edge_eq e). rewrite In_graph_aff_edge_in_AE in H. destruct H. intuition.
exists N0. rewrite <-(AE_weights _ _ H).
assert (eq (fst_ext e', snd_ext e', get_weight e) (fst_ext e, snd_ext e, get_weight e)) by Eq_comm_eq.
rewrite H3. rewrite <-(edge_eq e). rewrite In_graph_aff_edge_in_AE in H. destruct H. intuition.
rewrite <-(IE_weights _ _ H0). rewrite In_graph_interf_edge_in_IE in H0. destruct H0. rewrite (edge_eq e') in H2. intuition.
elim (interf_pref_conflict (fst_ext e') (snd_ext e') g).
unfold Prefere, Interfere; split.
exists N0. rewrite <-(AE_weights _ _ H0).
rewrite (edge_eq e') in H0. rewrite In_graph_aff_edge_in_AE in H0. destruct H0. auto.
rewrite <-(IE_weights _ _ H).
destruct H1; destruct H1.
assert (eq (fst_ext e', snd_ext e', get_weight e) (fst_ext e, snd_ext e, get_weight e)) by Eq_eq.
rewrite H3. rewrite <-(edge_eq e). rewrite In_graph_interf_edge_in_IE in H. destruct H. auto.
assert (eq (fst_ext e', snd_ext e', get_weight e) (fst_ext e, snd_ext e, get_weight e)) by Eq_comm_eq.
rewrite H3. rewrite <-(edge_eq e). rewrite In_graph_interf_edge_in_IE in H. destruct H. auto.
generalize (IE_weights _ _ H); intros.
generalize (IE_weights _ _ H0); intros.
destruct H1; destruct H1.
rewrite (edge_eq e). rewrite (edge_eq e'). rewrite H2. rewrite H3. Eq_eq.
rewrite (edge_eq e). rewrite (edge_eq e'). rewrite H2. rewrite H3. Eq_comm_eq.
Qed.

Lemma is_precolored_ext : forall x y g,
Vertex.eq x y ->
is_precolored x g = is_precolored y g.

Proof.
intros. apply compat_bool_is_precolored. assumption.
Qed.

(* This module respects the interface *)

(* A vertex x is in (remove_vertex r g) iff it is in g
   and it is different from r*)
Lemma In_remove_vertex : forall x r g,
In_graph x (remove_vertex r g) <-> (In_graph x g /\ ~Vertex.eq x r).

Proof.
split; intros.
split. apply in_remove_in with (r:=r). auto.
intro. rewrite H0 in H. elim (not_in_remove r g H).
destruct H. apply In_remove; auto.
Qed.

(* The precolored vertices of (remove_vertex r g) are
    the precolored vertices of g, minus r *)
Lemma precolored_remove_vertex : forall r g,
VertexSet.Equal (precolored (remove_vertex r g)) 
                          (VertexSet.remove r (precolored g)).

Proof.
split; intros.
rewrite precolored_remove_vertex2; auto.
rewrite <-precolored_remove_vertex2; auto.
Qed.

(* An edge e is in (remove_vertex r g) iff it is in g
   and is not incident to r *)
Lemma In_remove_edge : forall e r g,
In_graph_edge e (remove_vertex r g) <-> (In_graph_edge e g /\ ~incident e r).

Proof.
split; intros.
split. apply in_remove_in_edge with (r:=r). auto.
intro. elim (not_in_remove_edge _ _ _ H0 H).
destruct H. apply In_remove_edge_; auto.
Qed.

(* Specification of merge *)

(* A vertex is in (merge e g p q) iff x is in g and
    x is not equal to the second endpoint of g  *)
Lemma In_merge_vertex : forall g e x p q,
In_graph x (merge e g p q) <-> (In_graph x g /\ ~Vertex.eq x (snd_ext e)).

Proof.
split; intros.
split. apply (In_merge_in g e x p q H).
intro. rewrite H0 in H. elim (merge_1 e g p q H).
destruct H. apply merge_2; auto.
Qed.

(* If an interference edge e' is in the graph g then 
    its redirection from the second endpoint of e 
    to the first endpoint of e is in (merge e g p q) *)
Lemma In_merge_interf_edge : forall e e' g p q,
In_graph_edge e' g ->
interf_edge e' ->
In_graph_edge (redirect (snd_ext e) (fst_ext e) e') (merge e g p q).

Proof.
intros. apply merge_3; auto.
Qed.

(* If a preference edge e' different from e is in the graph g,
   and iff the endpoints of its redirection from the second
   endpoint of e to the first endpoint of e do not interfere,
   then these endpoints are linked with an affinity edge, whose
   weight may be different from the one of e' *)
Lemma In_merge_pref_edge : forall e e' g p q,
In_graph_edge e' g ->
~Edge.eq e e' ->
aff_edge e' ->
~Interfere (fst_ext (redirect (snd_ext e) (fst_ext e) e'))
                  (snd_ext (redirect (snd_ext e) (fst_ext e) e')) 
                  (merge e g p q) ->
    Prefere  (fst_ext (redirect (snd_ext e) (fst_ext e) e'))
                  (snd_ext (redirect (snd_ext e) (fst_ext e) e'))
                  (merge e g p q).

Proof.
intros. apply merge_5; auto.
Qed.

(* Inversely, if e' is an edge of (merge e g p q) then there exists
    an edge a of g, such that e' is weakly equal to the redirection
    of a from the second endpoint of e to the first endpoint of e *)
Lemma In_merge_edge_inv : forall e e' g p q,
In_graph_edge e' (merge e g p q) ->
exists a, In_graph_edge a g /\ weak_eq e' (redirect (snd_ext e) (fst_ext e) a) /\
              same_type a e'.

Proof.
intros. apply (merge_4 e e' g p q); auto.
Qed.

(* The precolored vertices of (merge e g p q) are the ones of g,
    minus the second endpoint of e *)
Lemma precolored_merge : forall e g p q,
VertexSet.Equal (precolored (merge e g p q))
                          (VertexSet.remove (snd_ext e) (precolored g)).

Proof.
split; intros.
rewrite <-precolored_merge2 in H. auto.
rewrite <-precolored_merge2. auto.
Qed.

(* Specification of delete_preference_edges *)

(* A vertex is in (delete_preference_edges r g p) iff it is in g *)
Lemma In_delete_preference_edges_vertex : forall x r g p,
In_graph x (delete_preference_edges r g p) <-> In_graph x g.

Proof.
unfold In_graph. split; intros.
rewrite <-V_delete_preference_eq in H. auto.
rewrite <-V_delete_preference_eq. auto.
Qed.

(* The precolored vertices of (delete_preference_edges r g p)
    iff it is precolored in g *)
Lemma precolored_delete_preference_edges : forall r g p,
VertexSet.Equal (precolored (delete_preference_edges r g p))
                          (precolored g).

Proof.
intros. apply delete_preference_edges_prec.
Qed.

(* An edge e is in (delete_preference_edges r g p) iff
   if is in g and it is not an affinity edge incident to r *)
Lemma In_delete_preference_edges_edge : forall e r g p,
In_graph_edge e (delete_preference_edges r g p) <-> 
(In_graph_edge e g /\ ~(aff_edge e /\ incident e r)).

Proof.
split; intros.
split. apply (delete_preference_edges_1 _ _ _ _ H).
intro. destruct H0.
assert (~incident e r). 
apply (in_delete_preference_not_incident e r g p).
rewrite In_graph_aff_edge_in_AE. split; auto.
elim (H2 H1).
destruct H. destruct H.
rewrite In_graph_aff_edge_in_AE in H. destruct H.
apply delete_preference_edges_2; auto.
right. rewrite <-IE_delete_preference_eq. auto.
Qed.

Definition interference_adj v g :=
adj_set v (imap g).

Definition preference_adj v g :=
adj_set v (pmap g).

(* Definition of the interference and preference degrees *)
Definition interf_degree g v := VertexSet.cardinal (interference_adj v g).
Definition pref_degree g v := VertexSet.cardinal (preference_adj v g).

(* Definition of the low-degree function,
    returns true iff the interference degree of v in g is strictly lower than K *)
Definition has_low_degree g K v :=
if le_lt_dec K (interf_degree g v) then false else true.

(* Definition of the move-related function,
    returns true iff the vertex is move-related *)
Definition move_related g x := negb (VertexSet.is_empty (preference_adj x g)).

Lemma in_pref_pref : forall x y g,
VertexSet.In x (preference_adj y g) ->
exists w, In_graph_edge (x,y,Some w) g.

Proof.
intros.
unfold preference_adj in H.
exists N0.
left. unfold AE.
rewrite edge_comm. apply (proj2 (edgemap_to_edgeset_charac _ _ _ _ (sym_pmap g))). assumption.
Qed.

Lemma pref_in_pref : forall x y g w,
In_graph_edge (x,y,Some w) g ->
VertexSet.In x (preference_adj y g).

Proof.
intros.
unfold preference_adj.
destruct H.
generalize (AE_weights _ _ H). intro.
unfold AE in H. simpl in H0. rewrite H0 in H.
rewrite edge_comm in H. apply (proj1 (edgemap_to_edgeset_charac _ _ _ _(sym_pmap g)) H).
generalize (proj1 (In_graph_interf_edge_in_IE _ _) H). intro.
destruct H0.
unfold interf_edge in H0. inversion H0.
Qed.

Lemma in_interf_interf : forall x y g,
VertexSet.In x (interference_adj y g) ->
In_graph_edge (x,y,None) g.

Proof.
intros.
unfold preference_adj in H.
right. unfold IE.
rewrite edge_comm. apply (proj2 (edgemap_to_edgeset_charac _ _ _ _ (sym_imap g))). assumption.
Qed.

Lemma interf_in_interf : forall x y g,
In_graph_edge (x,y,None) g ->
VertexSet.In x (interference_adj y g).

Proof.
intros.
unfold interference_adj.
destruct H.
generalize (AE_weights _ _ H). intro. inversion H0.
rewrite edge_comm in H. apply (proj1 (edgemap_to_edgeset_charac _ _ _ _(sym_imap g)) H).
Qed.

Lemma compat_interference_adj : forall x y g,
Vertex.eq x y ->
interference_adj x g = interference_adj y g.

Proof.
intros.
unfold interference_adj.
unfold adj_set.
rewrite (InterfFacts.find_o _ H). reflexivity.
Qed.

Lemma compat_preference_adj : forall x y g,
Vertex.eq x y ->
preference_adj x g = preference_adj y g.

Proof.
intros.
unfold preference_adj.
unfold adj_set.
rewrite (InterfFacts.find_o _ H). reflexivity.
Qed.

Lemma compat_bool_move : forall g, 
compat_bool Vertex.eq (move_related g).

Proof.
intros.
unfold compat_bool.
intros.
unfold move_related.
rewrite (compat_preference_adj _ _ _ H).
reflexivity.
Qed.

(* characterisation of move relation *)

Lemma move_related_charac : forall x g,
move_related g x = true ->
exists e, aff_edge e /\ In_graph_edge e g /\ incident e x.

Proof.
intros.
unfold move_related in H.
case_eq (VertexSet.is_empty (preference_adj x g)); intros.
rewrite H0 in H. inversion H. generalize H0. clear H H0. intro H.
case_eq (VertexSet.choose (preference_adj x g)); intros.
exists (x,e,Some N0).
split.
exists N0. auto.
generalize (VertexSet.choose_1 H0). clear H0. intro H0.
split.
left. unfold AE. apply (proj2 (edgemap_to_edgeset_charac _ _ _ _(sym_pmap g))).
assumption.
left. auto.
generalize (VertexSet.choose_2 H0). clear H0. intro H0.
rewrite (VertexSet.is_empty_1 H0) in H. inversion H.
Qed.

(* the inversion characterisation of move related *)

Lemma move_related_charac2 : forall x g e,
aff_edge e ->
In_graph_edge e g ->
incident e x ->
move_related g x = true.

Proof.
intros.
unfold move_related.
case_eq (VertexSet.is_empty (preference_adj x g)); intros.
generalize (VertexSet.is_empty_2 H2). clear H2. intro H2.
destruct H1.
elim (H2 (snd_ext e)).
apply pref_in_pref with (w:=N0).
rewrite edge_comm.
assert (eq (x,snd_ext e, Some N0) e).
apply eq_ordered_eq.
unfold E.eq; simpl; intuition. apply Regs.eq_refl.
destruct H0. generalize (AE_weights _ _ H0). intro.
rewrite <-H3. apply OptionN_as_OT.eq_refl.
generalize (proj1 (In_graph_interf_edge_in_IE _ _) H0). intros.
destruct H3.
unfold aff_edge in H. rewrite H3 in H. destruct H. inversion H.
rewrite H3. assumption.

elim (H2 (fst_ext e)).
apply pref_in_pref with (w:=N0).
assert (eq (fst_ext e, x, Some N0) e).
apply eq_ordered_eq.
unfold E.eq; simpl; intuition. apply Regs.eq_refl.
destruct H0. generalize (AE_weights _ _ H0). intro.
rewrite <-H3. apply OptionN_as_OT.eq_refl.
generalize (proj1 (In_graph_interf_edge_in_IE _ _) H0). intros.
destruct H3.
unfold aff_edge in H. rewrite H3 in H. destruct H. inversion H.
rewrite H3. assumption.
auto.
Qed.
Definition WS := (VertexSet.t*VertexSet.t*VertexSet.t*EdgeSet.t)%type.

Definition get_spillWL (w : WS) := fst (fst (fst w)).
Definition get_freezeWL (w : WS) := snd (fst (fst w)).
Definition get_simplifyWL (w : WS) := snd (fst w).
Definition get_movesWL (w : WS) := snd w.

Lemma compat_bool_low : forall g palette,
compat_bool Vertex.eq (has_low_degree g palette).

Proof.
unfold compat_bool. intros.
unfold has_low_degree, interf_degree.
rewrite (compat_interference_adj _ _ _ H).
reflexivity.
Qed.

Definition WS_properties g K (WL : WS) : Prop :=
(forall x, VertexSet.In x (get_spillWL WL) <-> has_low_degree g K x = false /\ In_graph x g /\ ~VertexSet.In x (precolored g)) /\
(forall x, VertexSet.In x (get_freezeWL WL) <-> has_low_degree g K x = true /\ (move_related g) x = true /\ ~VertexSet.In x (precolored g)) /\
(forall x, VertexSet.In x (get_simplifyWL WL) <-> has_low_degree g K x = true /\ (move_related g) x = false /\ In_graph x g /\ ~VertexSet.In x (precolored g)) /\
(forall e, EdgeSet.In e (get_movesWL WL) <-> aff_edge e /\ In_graph_edge e g).

Definition get_WL g palette :=
let not_pre := VertexSet.diff (V g) (precolored g) in
let (low, spill) := VertexSet.partition (has_low_degree g palette) not_pre in
let (free, simp) := VertexSet.partition (move_related g) low in
(spill, free, simp, AE g).

Module Import RegOTFacts := MyOTFacts Vertex.

Lemma move_related_in : forall g x,
move_related g x = true ->
In_graph x g.

Proof.
intros.
generalize (move_related_charac _ _ H). clear H. intro H.
destruct H as [e H]. destruct H. destruct H0.
apply (proj1 (extremities_pmap g x)).
destruct H0.
generalize (AE_weights _ _ H0). intro Hw.
unfold AE in *.
destruct H1.
rewrite (edge_eq e) in H0.
simpl in Hw. rewrite Hw in H0.
generalize (proj1 (edgemap_to_edgeset_charac _ _ _ _(sym_pmap g)) H0). intro H2.
apply (proj2 (InterfFacts.in_find_iff _ _)).
unfold adj_set in H2.
case_eq (VertexMap.find (fst_ext e) (pmap g)); intros; rewrite H3 in H2.
intro Helim.
rewrite (InterfFacts.find_o _ H1) in Helim.
rewrite H3 in Helim. inversion Helim.
elim (VertexSet.empty_1 H2).

rewrite (edge_eq e) in H0. rewrite edge_comm in H0.
simpl in Hw. rewrite Hw in H0.
generalize (proj1 (edgemap_to_edgeset_charac _ _ _ _(sym_pmap g)) H0). intro H2.
apply (proj2 (InterfFacts.in_find_iff _ _)).
unfold adj_set in H2.
case_eq (VertexMap.find (snd_ext e) (pmap g)); intros; rewrite H3 in H2.
intro Helim.
rewrite (InterfFacts.find_o _ H1) in Helim.
rewrite H3 in Helim. inversion Helim.
elim (VertexSet.empty_1 H2).

generalize (proj1 (In_graph_interf_edge_in_IE _ _) H0). intros.
destruct H2. unfold aff_edge in H. rewrite H2 in H. inversion H. inversion H4.
Qed.

Lemma WS_prop_get : forall g palette,
WS_properties g palette (get_WL g palette).

Proof.
intros.
unfold get_WL.
set (not_pre := VertexSet.diff (V g) (precolored g)) in *.
case_eq (VertexSet.partition (has_low_degree g palette) not_pre).
intros low spill H.
case_eq (VertexSet.partition (move_related g) low).
intros free simp H0.
unfold WS_properties.
unfold get_spillWL. unfold get_simplifyWL. unfold get_freezeWL. unfold get_movesWL. simpl.
assert (VertexSet.Equal low (VertexSet.filter (has_low_degree g palette) not_pre)).
assert (low = fst (VertexSet.partition (has_low_degree g palette) not_pre)).
rewrite H. auto.
rewrite H1. apply VertexSet.partition_1. apply compat_bool_low.
assert (VertexSet.Equal spill (VertexSet.filter (fun x => negb (has_low_degree g palette x)) not_pre)).
assert (spill = snd (VertexSet.partition (has_low_degree g palette) not_pre)).
rewrite H. auto.
rewrite H2. apply VertexSet.partition_2. apply compat_bool_low.
assert (VertexSet.Equal free (VertexSet.filter (move_related g) low)).
assert (free = fst (VertexSet.partition (move_related g) low)).
rewrite H0. auto.
rewrite H3. apply VertexSet.partition_1. apply compat_bool_move.
assert (VertexSet.Equal simp (VertexSet.filter (fun x => negb (move_related g x)) low)).
assert (simp = snd (VertexSet.partition (move_related g) low)).
rewrite H0. auto.
rewrite H4. apply VertexSet.partition_2. apply compat_bool_move.
split; intros.
split; intros.
rewrite H2 in H5.
split.
generalize (VertexSet.filter_2 (compat_not_compat (compat_bool_low _ _)) H5).
destruct (has_low_degree g palette x); intuition.
split.
generalize (VertexSet.filter_1 (compat_not_compat (compat_bool_low _ _)) H5). intro.
apply (VertexSet.diff_1 H6).
generalize (VertexSet.filter_1 (compat_not_compat (compat_bool_low _ _)) H5). intro.
apply (VertexSet.diff_2 H6).
rewrite H2.
apply VertexSet.filter_3.
apply compat_not_compat. apply compat_bool_low.
apply VertexSet.diff_3; intuition.
destruct H5. rewrite H5. auto.

split; intros.
split; intros.
rewrite H3 in H5.
generalize (VertexSet.filter_1 (compat_bool_move _) H5). intro H6.
generalize (VertexSet.filter_2 (compat_bool_move _) H5). clear H5. intro H5.
rewrite H1 in H6.
generalize (VertexSet.filter_1 (compat_bool_low _ _) H6). intro H7.
generalize (VertexSet.filter_2 (compat_bool_low _ _) H6). clear H6. intro H6.
generalize (VertexSet.diff_2 H7). intuition.

rewrite H3. apply VertexSet.filter_3.
apply compat_bool_move.
rewrite H1.
apply VertexSet.filter_3.
apply compat_bool_low.
apply VertexSet.diff_3.
apply move_related_in. intuition.
intuition.
intuition.
intuition.

split;intros.
split;intros.
rewrite H4 in H5.
generalize (VertexSet.filter_1 (compat_not_compat (compat_bool_move _)) H5). intro H6.
generalize (VertexSet.filter_2 (compat_not_compat (compat_bool_move _)) H5). clear H5. intro H5.
rewrite H1 in H6.
generalize (VertexSet.filter_1 (compat_bool_low _ _) H6). intro H7.
generalize (VertexSet.filter_2 (compat_bool_low _ _) H6). clear H6. intro H6.
generalize (VertexSet.diff_2 H7). intuition.
destruct (move_related g x); intuition.
apply (VertexSet.diff_1 H7).

rewrite H4.
apply VertexSet.filter_3.
apply compat_not_compat. apply compat_bool_move.
rewrite H1. apply VertexSet.filter_3.
apply compat_bool_low.
apply VertexSet.diff_3.
intuition.
intuition.
intuition.
destruct (move_related g x); intuition.
exact (In_graph_aff_edge_in_AE _ _).
Qed.

Definition not_incident_edges x s g := 
VertexSet.fold (fun y s' => EdgeSet.remove (x,y,Some N0) s')
               (adj_set x (pmap g))
	       s.

Lemma not_incident_edges_1 : forall x e s g,
(forall y, EdgeSet.In y s -> aff_edge y /\ In_graph_edge y g) ->
(EdgeSet.In e (not_incident_edges x s g) <->
 EdgeSet.In e s /\ ~incident e x).

Proof.
split; intros.
unfold not_incident_edges in H0.
rewrite VertexSet.fold_1 in H0.
assert (EdgeSet.In e s) as Hin.
induction (VertexSet.elements (adj_set x (pmap g))). simpl in H0.
assumption.
rewrite MEdgeFacts.fold_left_assoc in H0.
apply IHl.
apply (EdgeSet.remove_3 H0).

intros.
split; intros.
apply EdgeSet.remove_2. intro.
generalize (EdgeSet.remove_3 H1). intro.
elim (EdgeSet.remove_1 H2 H3).
apply EdgeSet.remove_2. intro.
elim (EdgeSet.remove_1 H2 H1).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H1)).
apply EdgeSet.remove_2. intro.
generalize (EdgeSet.remove_3 H1). intro.
elim (EdgeSet.remove_1 H2 H3).
apply EdgeSet.remove_2. intro.
elim (EdgeSet.remove_1 H2 H1).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H1)).
intros. apply RegRegProps.Equal_remove. assumption.

split.
assumption.

generalize VertexSet.elements_1. intro HH.
intro Helim. destruct Helim.
generalize (HH (adj_set x (pmap g)) (snd_ext e)). clear HH. intro HH.
induction (VertexSet.elements (adj_set x (pmap g))). simpl in H0.

assert (VertexSet.In (snd_ext e) (adj_set x (pmap g))).
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))).
assert (eq e (x, snd_ext e, Some N0)).
assert (get_weight e = Some N0).

generalize (H _ H0). intro.
destruct H2. unfold In_graph_edge in H3.
destruct H3.
apply (AE_weights g). assumption.
generalize (IE_weights g _ H3). intro.
destruct H2. congruence.
rewrite <-H2. Eq_eq. apply Regs.eq_refl.
rewrite <-H2. 

generalize (H _ H0). intro.
destruct H3. destruct H4.
assumption.
generalize (IE_weights g _ H4). intro.
destruct H3. congruence.

generalize (HH H2). intro. inversion H3.

rewrite MEdgeFacts.fold_left_assoc in H0.
apply IHl.
apply (EdgeSet.remove_3 H0).

intro. generalize (HH H2). clear HH H2. intro H2.
inversion H2; subst.
assert (eq e (x, a, Some N0)).
rewrite (edge_eq e).
apply eq_ordered_eq.
constructor. simpl. split; intuition.
simpl.

generalize (H _ Hin). intro H5.
destruct H5.
destruct H5.
rewrite (AE_weights g _ H5). apply OptionN_as_OT.eq_refl.
generalize (IE_weights g _ H5). intro. destruct H3. congruence.
elim (EdgeSet.remove_1 (eq_sym H3) H0). 
assumption.

intros.
split; intros.
apply EdgeSet.remove_2. intro.
generalize (EdgeSet.remove_3 H2). intro.
elim (EdgeSet.remove_1 H3 H4).
apply EdgeSet.remove_2. intro.
elim (EdgeSet.remove_1 H3 H2).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H2)).
apply EdgeSet.remove_2. intro.
generalize (EdgeSet.remove_3 H2). intro.
elim (EdgeSet.remove_1 H3 H4).
apply EdgeSet.remove_2. intro.
elim (EdgeSet.remove_1 H3 H2).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H2)).
intros. apply RegRegProps.Equal_remove. assumption.

generalize (HH (adj_set x (pmap g)) (fst_ext e)). clear HH. intro HH.
induction (VertexSet.elements (adj_set x (pmap g))). simpl in H0.

assert (VertexSet.In (fst_ext e) (adj_set x (pmap g))).
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))).
assert (eq e (x, fst_ext e, Some N0)).
assert (get_weight e = Some N0).

generalize (H _ H0). intro.
destruct H2. unfold In_graph_edge in H3.
destruct H3.
apply (AE_weights g). assumption.
generalize (IE_weights g _ H3). intro.
destruct H2. congruence.
rewrite <-H2. Eq_comm_eq. apply Regs.eq_refl.
rewrite <-H2. 

generalize (H _ H0). intro.
destruct H3. destruct H4.
assumption.
generalize (IE_weights g _ H4). intro.
destruct H3. congruence.

generalize (HH H2). intro. inversion H3.

rewrite MEdgeFacts.fold_left_assoc in H0.
apply IHl.
apply (EdgeSet.remove_3 H0).

intro. generalize (HH H2). clear HH H2. intro H2.
inversion H2; subst.
assert (eq e (x, a, Some N0)).
rewrite (edge_eq e).
rewrite edge_comm. apply eq_ordered_eq.
constructor. simpl. split; intuition.
simpl.

generalize (H _ Hin). intro H5.
destruct H5.
destruct H5.
rewrite (AE_weights g _ H5). apply OptionN_as_OT.eq_refl.
generalize (IE_weights g _ H5). intro. destruct H3. congruence.
elim (EdgeSet.remove_1 (eq_sym H3) H0). 
assumption.

intros.
split; intros.
apply EdgeSet.remove_2. intro.
generalize (EdgeSet.remove_3 H2). intro.
elim (EdgeSet.remove_1 H3 H4).
apply EdgeSet.remove_2. intro.
elim (EdgeSet.remove_1 H3 H2).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H2)).
apply EdgeSet.remove_2. intro.
generalize (EdgeSet.remove_3 H2). intro.
elim (EdgeSet.remove_1 H3 H4).
apply EdgeSet.remove_2. intro.
elim (EdgeSet.remove_1 H3 H2).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H2)).
intros. apply RegRegProps.Equal_remove. assumption.

unfold not_incident_edges.
rewrite VertexSet.fold_1.
induction (VertexSet.elements (adj_set x (pmap g))). simpl.
intuition.
rewrite MEdgeFacts.fold_left_assoc.
apply EdgeSet.remove_2.
destruct H0.
intro H2. elim H1.
destruct (eq_charac _ _ H2); destruct H3; change_rewrite.
left. auto.
right. auto.
assumption.

intros.
split; intros.
apply EdgeSet.remove_2. intro.
generalize (EdgeSet.remove_3 H1). intro.
elim (EdgeSet.remove_1 H2 H3).
apply EdgeSet.remove_2. intro.
elim (EdgeSet.remove_1 H2 H1).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H1)).
apply EdgeSet.remove_2. intro.
generalize (EdgeSet.remove_3 H1). intro.
elim (EdgeSet.remove_1 H2 H3).
apply EdgeSet.remove_2. intro.
elim (EdgeSet.remove_1 H2 H1).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H1)).
intros. apply RegRegProps.Equal_remove. assumption.
Qed.

Definition not_incident_merge x s es :=
VertexSet.fold (fun y s' => EdgeSet.remove (x,y,Some N0) s')
               es s.

Lemma not_incident_merge_1 : forall x s es e,
EdgeSet.In e (not_incident_merge x es s) ->
EdgeSet.In e es.

Proof.
unfold not_incident_merge; intros.
set (f :=  (fun (y : VertexSet.elt) (s' : EdgeSet.t) =>
          EdgeSet.remove (x, y, Some 0%N) s')) in *.
rewrite VertexSet.fold_1 in H.
set (f' := fun a e => f e a) in *.
induction (VertexSet.elements s). simpl in H. assumption.
rewrite MEdgeFacts.fold_left_assoc in H.
set (tmp := fold_left f' l es) in H.
unfold f' in H. unfold f in H.
apply (IHl (EdgeSet.remove_3 H)).

unfold f'. unfold f. intros.
split; intros.
apply EdgeSet.remove_2.
intro H1. elim (EdgeSet.remove_1 H1 (EdgeSet.remove_3 H0)).
apply EdgeSet.remove_2.
intro H1. elim (EdgeSet.remove_1 H1 H0).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H0)).
apply EdgeSet.remove_2.
intro H1. elim (EdgeSet.remove_1 H1 (EdgeSet.remove_3 H0)).
apply EdgeSet.remove_2.
intro H1. elim (EdgeSet.remove_1 H1 H0).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H0)).

intros.
unfold f'. unfold f.
apply RegRegProps.Equal_remove. auto.
Qed.


Definition AE_merge_up newadj adj adjsnd e es :=
let diff1 := VertexSet.diff adj newadj in
let diff2 := VertexSet.diff newadj adj in
let new_es := not_incident_merge (snd_ext e)
                  (not_incident_merge (fst_ext e) es diff1)
             adjsnd in
VertexSet.fold (fun y s'' => EdgeSet.add (fst_ext e,y,Some N0) s'')
               diff2 new_es.

Lemma not_incident_merge_2 : forall x y s s',
EdgeSet.In (x,y,Some N0) (not_incident_merge x s s') ->
~VertexSet.In y s'.

Proof.
intros.
unfold not_incident_merge in H.
set (f :=  (fun (y : VertexSet.elt) (s' : EdgeSet.t) =>
          EdgeSet.remove (x, y, Some 0%N) s')) in *.
rewrite VertexSet.fold_1 in H.
set (f' := fun a e => f e a) in *.
generalize VertexSet.elements_1. intro HH.
generalize (HH s' y). clear HH. intro HH.
induction (VertexSet.elements s'). simpl in H.
intro. generalize (HH H0). intro H1. inversion H1.
rewrite MEdgeFacts.fold_left_assoc in H.
set (tmp := fold_left f' l s) in *.
unfold f' in H. unfold f in H.
destruct (Vertex.eq_dec y a).
cut (eq (x,y,Some N0) (x,a, Some N0)). intro H0.
elim (EdgeSet.remove_1 (Edge.eq_sym H0) H).
apply eq_ordered_eq. constructor;simpl; try split; intuition.
apply OptionN_as_OT.eq_refl.
apply IHl. apply (EdgeSet.remove_3 H).
intro. generalize (HH H0). intro H1.
inversion H1; subst.
elim (n H3).
auto.

unfold f'. unfold f. intros.
split; intros.
apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 (EdgeSet.remove_3 H0)).
apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 H0).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H0)).

apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 (EdgeSet.remove_3 H0)).
apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 H0).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H0)).

unfold f'. unfold f. intros.
apply RegRegProps.Equal_remove. auto.
Qed.

Lemma AE_merge_wl_1 : forall x y e g,
aff_edge e ->
In_graph_edge e g ->
(VertexSet.In x (adj_set y (pmap_merge e g (imap_merge e g))) <->
(VertexSet.In x (adj_set y (map_merge e (pmap g))) /\
~VertexSet.In x (adj_set y (imap_merge e g)))).

Proof.
intros x y e g p q. split; intros.
split.
apply pmap_merge_sub. assumption.
intro. apply (simple_graph (merge e g q p) x y). intuition.
destruct H.
unfold merge. simpl. apply resolve_conflicts_map_5; auto.
Qed.

Lemma not_in_diff_equiv : forall x s s',
~VertexSet.In x (VertexSet.diff s s') ->
VertexSet.In x s' \/ ~VertexSet.In x s.

Proof.
intros. destruct (Props.In_dec x s).
           destruct (Props.In_dec x s').
left. auto.
elim H. apply VertexSet.diff_3; auto.
right. auto.
Qed.

Lemma AE_aux_2 : forall e g s p q,
(forall a, EdgeSet.In a s <-> aff_edge a /\ In_graph_edge a g) ->
(forall b, EdgeSet.In b (AE_merge_up (preference_adj (fst_ext e) (merge e g p q))
                                     (preference_adj (fst_ext e) g)
                                     (preference_adj (snd_ext e) g)
                                     e s) 
           <->
           (~incident b (snd_ext e) /\
           ((EdgeSet.In b s /\ ~Interfere (fst_ext b) (snd_ext b) (merge e g p q)) \/  
            EdgeSet.In b (VertexSet.fold 
                            (fun y s' => EdgeSet.add (fst_ext e, y, Some N0) s')
                            (preference_adj (fst_ext e) (merge e g p q))
                            EdgeSet.empty)))).

Proof.
intros e g s p q; split; intros.
unfold AE_merge_up in H0.
set (f := (fun (y : VertexSet.elt) (s'' : EdgeSet.t) =>
           EdgeSet.add (fst_ext e, y, Some 0%N) s'')) in *.
set (diff1 := (VertexSet.diff (preference_adj (fst_ext e) (merge e g p q))
             (preference_adj (fst_ext e) g))) in *.
set (diff2 :=  (VertexSet.diff (preference_adj (fst_ext e) g)
                   (preference_adj (fst_ext e) (merge e g p q)))) in *.
cut (get_weight b = Some N0). intro Hw.
cut (~incident b (snd_ext e)). intro Hcut.
split.
assumption.
rewrite VertexSet.fold_1 in H0.
set (f' := fun a e => f e a) in *.
generalize VertexSet.elements_2. intro HH.
generalize (HH diff1). clear HH. intro HH.
induction (VertexSet.elements diff1). simpl in H0.
left. split.
apply (not_incident_merge_1 _ _ _ _ (not_incident_merge_1 _ _ _ _ H0)).
intro H1. unfold Interfere in H1.
generalize (merge_4 e (fst_ext b, snd_ext b, None) _ p q H1). intro H2.
destruct H2. destruct H2.
unfold redirect in H3.
destruct (OTFacts.eq_dec (fst_ext x) (snd_ext e)). destruct H3.
assert (eq (fst_ext b, snd_ext b, None) (fst_ext e, snd_ext x, get_weight x)).
unfold weak_eq in H3. change_rewrite. destruct H3.
apply eq_ordered_eq; split; simpl; auto.
unfold same_type in H4. destruct H4.
destruct H4. destruct H5. simpl in H5. inversion H5.
destruct H4. rewrite <-H4. apply OptionN_as_OT.eq_refl.
destruct H3.
unfold same_type in H4. destruct H4.
destruct H4. destruct H6. simpl in H6. inversion H6.
destruct H4. rewrite <-H4. rewrite edge_comm. apply eq_ordered_eq.
split; auto. simpl. apply OptionN_as_OT.eq_refl.
generalize H5. clear H3 H4 H5. intro H3.
destruct (eq_charac _ _ H3); destruct H4; change_rewrite.
generalize (not_incident_merge_1 _ _ _ _ H0). intro H6.
cut (eq b (fst_ext e, snd_ext x, Some N0)). intro H7.
rewrite H7 in H6. clear H7.
generalize (not_incident_merge_2 _ _ _ _ H6). intro H7.
unfold diff2 in H7.
generalize (not_in_diff_equiv _ _ _ H7). clear H7. intro H7. destruct H7.
rewrite <-H5 in H7. generalize (sym_pmap_merge_map e g q p _ _ H7). intro H8.
rewrite <-H4 in H8. generalize (sym_pmap_merge_map e g q p _ _ H8). intro H9.
elim (simple_graph (merge e g p q) (snd_ext b) (fst_ext b)). split.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ None (sym_imap_merge_map e g q p))).
destruct H1.
generalize (AE_weights _ _ H1). simpl. congruence.
assumption.
assumption.
rewrite <-H5 in H7.
elim H7. apply (sym_pmap g).
rewrite <-H4.
cut (In_graph_edge b g).
intro H8.
destruct H8.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))).
cut (eq b (snd_ext b, fst_ext b, Some N0)). intro H9.
rewrite <-H9. assumption.
rewrite edge_comm. rewrite (edge_eq b). change_rewrite.
rewrite Hw. apply eq_refl.
generalize (IE_weights _ _ H8). congruence.
generalize (proj1 (H _) (not_incident_merge_1 _ _ _ _ (not_incident_merge_1 _ _ _ _ H0))).
intuition.
apply eq_ordered_eq.
constructor; simpl. split. auto. auto.
fold (get_weight b). rewrite Hw. apply OptionN_as_OT.eq_refl.

generalize (not_incident_merge_1 _ _ _ _ H0). intro H6.
cut (eq b (fst_ext e, snd_ext x, Some N0)). intro H7.
rewrite H7 in H6. clear H7.
generalize (not_incident_merge_2 _ _ _ _ H6). intro H7.
unfold diff2 in H7.
generalize (not_in_diff_equiv _ _ _ H7). clear H7. intro H7.
destruct H7.
rewrite <-H4 in H7. generalize (sym_pmap_merge_map e g q p _ _ H7). intro H8.
rewrite <-H5 in H8. generalize (sym_pmap_merge_map e g q p _ _ H8). intro H9.
elim (simple_graph (merge e g p q) (snd_ext b) (fst_ext b)). split.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ None (sym_imap_merge_map e g q p))).
destruct H1.
generalize (AE_weights _ _ H1). simpl. congruence.
assumption.
assumption.
rewrite <-H4 in H7.
elim H7. apply (sym_pmap g).
rewrite <-H5.
cut (In_graph_edge b g).
intro H8.
destruct H8.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))).
cut (eq b (snd_ext b, fst_ext b, Some N0)). intro H9.
rewrite edge_comm. rewrite <-H9. assumption.
rewrite edge_comm. rewrite (edge_eq b). change_rewrite.
rewrite Hw. apply eq_refl.
generalize (IE_weights _ _ H8). congruence.
generalize (proj1 (H _) (not_incident_merge_1 _ _ _ _ (not_incident_merge_1 _ _ _ _ H0))).
intuition.
rewrite edge_comm. apply eq_ordered_eq.
constructor; simpl. split. auto. auto.
fold (get_weight b). rewrite Hw. apply OptionN_as_OT.eq_refl.

destruct (OTFacts.eq_dec (snd_ext x) (snd_ext e)).
assert (eq (fst_ext b, snd_ext b, None) (fst_ext x, fst_ext e, get_weight x)).
destruct H3. unfold same_type in H4. destruct H4; destruct H4.
destruct H5. simpl in H5. inversion H5. rewrite <-H4.
unfold weak_eq in H3. change_rewrite.
destruct H3; destruct H3.
apply eq_ordered_eq. split; auto. simpl. apply OptionN_as_OT.eq_refl.
rewrite edge_comm. apply eq_ordered_eq. split; auto. simpl. apply OptionN_as_OT.eq_refl.
generalize H4. clear H3 H4. intro H3.
destruct (eq_charac _ _ H3); change_rewrite. destruct H4.
generalize (not_incident_merge_1 _ _ _ _ H0). intro H6.
cut (eq b (fst_ext e, fst_ext x, Some N0)). intro H7.
rewrite H7 in H6. clear H7.
generalize (not_incident_merge_2 _ _ _ _ H6). intro H7.
unfold diff2 in H7.
generalize (not_in_diff_equiv _ _ _ H7). clear H7. intro H7.
destruct H7.
rewrite <-H4 in H7. generalize (sym_pmap_merge_map e g q p _ _ H7). intro H8.
rewrite <-H5 in H8. generalize (sym_pmap_merge_map e g q p _ _ H8). intro H9.
elim (simple_graph (merge e g p q) (snd_ext b) (fst_ext b)). split.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ None (sym_imap_merge_map e g q p))).
destruct H1.
generalize (AE_weights _ _ H1). simpl. congruence.
assumption.
assumption.
rewrite <-H4 in H7.
elim H7. apply (sym_pmap g).
rewrite <-H5.
cut (In_graph_edge b g).
intro H8.
destruct H8.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))).
cut (eq b (fst_ext b, snd_ext b, Some N0)). intro H9.
rewrite <-H9. assumption.
rewrite (edge_eq b). change_rewrite.
rewrite Hw. apply eq_refl.
generalize (IE_weights _ _ H8). congruence.
generalize (proj1 (H _) (not_incident_merge_1 _ _ _ _ (not_incident_merge_1 _ _ _ _ H0))).
intuition.
rewrite edge_comm. apply eq_ordered_eq.
constructor; simpl. split. auto. auto.
fold (get_weight b). rewrite Hw. apply OptionN_as_OT.eq_refl.

destruct H4.
generalize (not_incident_merge_1 _ _ _ _ H0). intro H6.
cut (eq b (fst_ext e, fst_ext x, Some N0)). intro H7.
rewrite H7 in H6. clear H7.
generalize (not_incident_merge_2 _ _ _ _ H6). intro H7.
unfold diff2 in H7.
generalize (not_in_diff_equiv _ _ _ H7). clear H7. intro H7.
destruct H7.
rewrite <-H5 in H7. generalize (sym_pmap_merge_map e g q p _ _ H7). intro H8.
rewrite <-H4 in H8. generalize (sym_pmap_merge_map e g q p _ _ H8). intro H9.
elim (simple_graph (merge e g p q) (snd_ext b) (fst_ext b)). split.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ None (sym_imap_merge_map e g q p))).
destruct H1.
generalize (AE_weights _ _ H1). simpl. congruence.
assumption.
assumption.
rewrite <-H5 in H7.
elim H7. apply (sym_pmap g).
rewrite <-H4.
cut (In_graph_edge b g).
intro H8.
destruct H8.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))).
cut (eq b (fst_ext b, snd_ext b, Some N0)). intro H9.
rewrite edge_comm. rewrite <-H9. assumption.
rewrite (edge_eq b). change_rewrite.
rewrite Hw. apply eq_refl.
generalize (IE_weights _ _ H8). congruence.
generalize (proj1 (H _) (not_incident_merge_1 _ _ _ _ (not_incident_merge_1 _ _ _ _ H0))).
intuition.
apply eq_ordered_eq.
constructor; simpl. split. auto. auto.
fold (get_weight b). rewrite Hw. apply OptionN_as_OT.eq_refl.

assert (eq (fst_ext b, snd_ext b, None) x).
destruct H3. unfold same_type in H4. destruct H4; destruct H4.
destruct H5. simpl in H5. inversion H5.
rewrite <-H4.
unfold weak_eq in H3; change_rewrite. destruct H3; destruct H3.
apply eq_ordered_eq; split; auto. apply OptionN_as_OT.eq_refl.
rewrite edge_comm. apply eq_ordered_eq; split; auto. apply OptionN_as_OT.eq_refl.
generalize H4. clear H3 H4. intro H3.
elim (simple_graph g (fst_ext b) (snd_ext b)).
split.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ None (sym_imap g))).
rewrite edge_comm. rewrite H3.
destruct H2.
rewrite <-H3 in H2. generalize (AE_weights _ _ H2). simpl. congruence.
assumption.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))).
assert (In_graph_edge b g).
generalize (proj1 (H _) (not_incident_merge_1 _ _ _ _ (not_incident_merge_1 _ _ _ _ H0))).
intuition.
destruct H4.
assert (eq b (fst_ext b, snd_ext b, Some N0)).
rewrite (edge_eq b). change_rewrite.
rewrite Hw. apply eq_refl.
rewrite edge_comm. rewrite <-H5. assumption.
generalize (IE_weights _ _ H4). congruence.
rewrite MEdgeFacts.fold_left_assoc in H0.
set (set := (not_incident_merge (snd_ext e)
                (not_incident_merge (fst_ext e) s diff2)
                (preference_adj (snd_ext e) g))) in *.
set (tmp := fold_left f' l set) in *.
unfold f' in H0. unfold f in H0.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H0).
fold (eq (fst_ext e, a, Some N0) b) in H1.
right.
rewrite <-H1.
rewrite VertexSet.fold_1.
fold f'.
set (s' := preference_adj (fst_ext e) (merge e g p q)) in *.
generalize VertexSet.elements_1. intro HHH.
generalize (HHH s' a). clear HHH. intro HHH.
induction  (VertexSet.elements s'). simpl.
assert (InA Vertex.eq a nil).
apply HHH.
unfold s'.
assert (VertexSet.In a diff1).
apply HH. left. intuition.
apply (VertexSet.diff_1 H2). inversion H2.
rewrite MEdgeFacts.fold_left_assoc.
set (tmp' := fold_left f' l0 EdgeSet.empty) in *.
unfold f'. unfold f.
destruct (Vertex.eq_dec a a0).
apply EdgeSet.add_1.
apply eq_ordered_eq. constructor;simpl.
split; intuition.
apply OptionN_as_OT.eq_refl.
apply EdgeSet.add_2.
apply IHl0. intros.
generalize (HHH H2). intro.
inversion H3; subst.
elim (n H5).
auto.

unfold f'. unfold f. intros.
apply RegRegProps.add_add.

unfold f'. unfold f. intros.
apply RegRegProps.Dec.F.add_m. apply eq_refl. auto.

apply IHl.
assumption.
intros.
apply HH.
right. auto.

unfold f'. unfold f. intros.
apply RegRegProps.add_add.

unfold f'. unfold f. intros.
apply RegRegProps.Dec.F.add_m. apply eq_refl. auto.

rewrite VertexSet.fold_1 in H0.
set (f' := fun a e => f e a) in *.
generalize VertexSet.elements_2. intro HH.
generalize (HH diff1). clear HH. intro HH.
induction (VertexSet.elements diff1). simpl in H0.
intro Hinc. destruct Hinc.
assert (eq b (snd_ext e, snd_ext b, Some N0)).
rewrite (edge_eq b). change_rewrite. rewrite Hw.
apply eq_ordered_eq.
constructor;simpl. split;intuition.
apply OptionN_as_OT.eq_refl.

rewrite H2 in H0.
generalize (not_incident_merge_2 _ _ _ _ H0). intro H3.
elim H3.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))). rewrite <-H2.
assert (In_graph_edge b g).
generalize (proj1 (H _) (not_incident_merge_1 _ _ _ _ (not_incident_merge_1 _ _ _ _ H0))).
intro. destruct H4. rewrite <-H2 in H5. assumption.
destruct H4.
assumption.
generalize (IE_weights _ _ H4). congruence.

assert (eq b (fst_ext b, snd_ext e, Some N0)).
rewrite (edge_eq b). change_rewrite. rewrite Hw.
apply eq_ordered_eq.
constructor;simpl. split; intuition.
apply OptionN_as_OT.eq_refl.

rewrite H2 in H0. rewrite edge_comm in H0.
generalize (not_incident_merge_2 _ _ _ _ H0). intro H3.
elim H3.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))). rewrite edge_comm. rewrite <-H2.
assert (In_graph_edge b g).
generalize (proj1 (H _) (not_incident_merge_1 _ _ _ _ (not_incident_merge_1 _ _ _ _ H0))).
intro. destruct H4. rewrite edge_comm in H2. rewrite <-H2 in H5. assumption.
destruct H4.
assumption.
generalize (IE_weights _ _ H4). congruence.

rewrite MEdgeFacts.fold_left_assoc in H0.
set (set := (not_incident_merge (snd_ext e)
                (not_incident_merge (fst_ext e) s diff2)
                (preference_adj (snd_ext e) g))) in *.
set (tmp := fold_left f' l set) in *.
unfold f' in H0. unfold f in H0.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H0).
fold (eq (fst_ext e, a, Some N0) b) in H1.
intro. destruct H2.
destruct (eq_charac _ _ H1); change_rewrite. destruct H3.
elim (In_graph_edge_diff_ext _ _ p).
apply Vertex.eq_trans with (y := fst_ext b); auto.
destruct H3.
assert  (VertexSet.In a diff1). apply HH.
left. intuition.
unfold diff1 in H5. generalize (VertexSet.diff_2 H5). clear H5. intro H5.
elim H5.
rewrite H4. rewrite <-H2.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))).
generalize p. intro Hin.
destruct Hin.
assert (eq (fst_ext e, snd_ext e, Some N0) e).
apply eq_ordered_eq.
constructor. simpl. split; apply Regs.eq_refl.
simpl. fold (get_weight e). rewrite (AE_weights _ _ H6).
apply OptionN_as_OT.eq_refl.
rewrite H7. assumption.
generalize (IE_weights _ _ H6). generalize q. intro Haff. destruct Haff. congruence.

destruct (eq_charac _ _ H1); change_rewrite. destruct H3.
assert  (VertexSet.In a diff1). apply HH.
left. intuition.
unfold diff1 in H5. generalize (VertexSet.diff_2 H5). clear H5. intro H5.
elim H5.
rewrite H4. rewrite <-H2.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))).
generalize p. intro Hin.
destruct Hin.
assert (eq (fst_ext e, snd_ext e, Some N0) e).
apply eq_ordered_eq.
constructor. simpl. split; apply Regs.eq_refl.
simpl. fold (get_weight e). rewrite (AE_weights _ _ H6).
apply OptionN_as_OT.eq_refl.
rewrite H7. assumption.
generalize (IE_weights _ _ H6). generalize q. intro Haff. destruct Haff. congruence.
elim (In_graph_edge_diff_ext _ _ p).
apply Vertex.eq_trans with (y := snd_ext b); auto.
destruct H3. auto.
apply IHl. auto.
intros. apply HH. right. auto.

unfold f'. unfold f. intros.
apply RegRegProps.add_add.

unfold f'. unfold f. intros.
apply RegRegProps.Dec.F.add_m. apply eq_refl. auto.

rewrite VertexSet.fold_1 in H0.
set (f' := fun a e => f e a) in *.
induction (VertexSet.elements diff1). simpl in H0.
assert (aff_edge b /\ In_graph_edge b g).
rewrite <-H.
apply (not_incident_merge_1 _ _ _ _ (not_incident_merge_1 _ _ _ _ H0)).
destruct H1.
destruct H2.
apply (AE_weights _ _ H2).
destruct H1. generalize (IE_weights _ _ H2). congruence.

rewrite MEdgeFacts.fold_left_assoc in H0.
set (set := (not_incident_merge (snd_ext e)
                (not_incident_merge (fst_ext e) s diff2)
                (preference_adj (snd_ext e) g))) in *.
set (tmp := fold_left f' l set) in *.
unfold f' in H0. unfold f in H0.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H0).
fold (eq (fst_ext e, a, Some N0) b) in H1.
rewrite <-H1. auto.
apply IHl. auto.

unfold f'. unfold f. intros.
apply RegRegProps.add_add.

unfold f'. unfold f. intros.
apply RegRegProps.Dec.F.add_m. apply eq_refl. auto.

destruct H0.
destruct H1.
destruct H1.
unfold AE_merge_up.
set (f :=  (fun (y : VertexSet.elt) (s'' : EdgeSet.t) =>
      EdgeSet.add (fst_ext e, y, Some 0%N) s'')) in *.
set (diff1 := (VertexSet.diff (preference_adj (fst_ext e) (merge e g p q))
             (preference_adj (fst_ext e) g))) in *.
set (diff2 :=  (VertexSet.diff (preference_adj (fst_ext e) g)
                   (preference_adj (fst_ext e) (merge e g p q)))) in *.
cut (EdgeSet.In b (not_incident_merge (snd_ext e) 
                       (not_incident_merge (fst_ext e) s diff2)
                  (preference_adj (snd_ext e) g))). intro H3.
rewrite VertexSet.fold_1.
set (f' := fun a e => f e a) in *.
induction (VertexSet.elements diff1). simpl. assumption.
rewrite MEdgeFacts.fold_left_assoc.
set (set := (fold_left f' l
           (not_incident_merge (snd_ext e)
              (not_incident_merge (fst_ext e) s diff2)
              (preference_adj (snd_ext e) g)))) in *.
unfold f'. unfold f.
apply EdgeSet.add_2. assumption.

unfold f'. unfold f. intros.
apply RegRegProps.add_add.

unfold f'. unfold f. intros.
apply RegRegProps.Dec.F.add_m. apply eq_refl. auto.

cut (EdgeSet.In b (not_incident_merge (fst_ext e) s diff2)). intro.
set (set := (not_incident_merge (fst_ext e) s diff2)) in *.
unfold not_incident_merge.
set (h := (fun (y : VertexSet.elt) (s' : EdgeSet.t) =>
      EdgeSet.remove (snd_ext e, y, Some 0%N) s')) in *.
set (adjsnd := preference_adj (snd_ext e) g) in *.
rewrite VertexSet.fold_1.
set (h' := fun a e => h e a) in *.
induction (VertexSet.elements adjsnd). simpl. assumption.
rewrite MEdgeFacts.fold_left_assoc.
set (tmp := fold_left h' l set) in *.
unfold h'. unfold h.
apply EdgeSet.remove_2.
intro. elim H0.
destruct (eq_charac _ _ H4); change_rewrite; destruct H5.
left. auto.
right. auto. assumption.

unfold h'. unfold h. intros.
split; intros.
apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 (EdgeSet.remove_3 H4)).
apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 H4).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H4)).

apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 (EdgeSet.remove_3 H4)).
apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 H4).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H4)).

unfold h'. unfold h. intros.
apply RegRegProps.Equal_remove. auto.

unfold not_incident_merge.
set (h := (fun (y : VertexSet.elt) (s' : EdgeSet.t) =>
      EdgeSet.remove (fst_ext e, y, Some 0%N) s')) in *.
rewrite VertexSet.fold_1.
set (h' := fun a e => h e a) in *.
generalize VertexSet.elements_2. intro.
generalize (H3 diff2). clear H3. intro HH.
induction (VertexSet.elements diff2). simpl. assumption.
rewrite MEdgeFacts.fold_left_assoc.
set (tmp := fold_left h' l s) in *.
unfold h'. unfold h.
apply EdgeSet.remove_2.
intro.
assert (VertexSet.In a diff2).
apply HH. left. intuition.
unfold diff2 in H4.
elim (VertexSet.diff_2 H4). clear H4.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap_merge_map e g q p))).
assert (eq (fst_ext e, a, Some N0) b). auto. generalize H4. clear H3 H4. intro H3.
rewrite H3.
cut (eq b (fst_ext b, snd_ext b, Some N0)). intro.
rewrite H4.
cut (In_graph_edge (fst_ext b, snd_ext b, Some N0) (merge e g p q)). intro.
destruct H5. assumption.
generalize (IE_weights _ _ H5). simpl. congruence.
rewrite <-H4.
cut (eq b (redirect (snd_ext e) (fst_ext e) b)). intro.
rewrite H5. rewrite (edge_eq _).
cut (get_weight (redirect (snd_ext e) (fst_ext e) b) = Some N0). intro.
rewrite H6.
assert (exists w, In_graph_edge
  (fst_ext (redirect (snd_ext e) (fst_ext e) b),
  snd_ext (redirect (snd_ext e) (fst_ext e) b), Some w) (merge e g p q)).
apply merge_5.

rewrite H in H1. intuition.
intro.
elim H0.
destruct (eq_charac _ _ H7);change_rewrite; destruct H8.
right. auto.
left. auto.
unfold aff_edge. exists N0. rewrite <-H3. auto.

cut (eq (fst_ext (redirect (snd_ext e) (fst_ext e) b),
         snd_ext (redirect (snd_ext e) (fst_ext e) b),
         None) (fst_ext b, snd_ext b, None)). intro.
unfold Interfere. rewrite H7. assumption.

unfold redirect. destruct (OTFacts.eq_dec (fst_ext b) (snd_ext e)).
elim H0. left. auto.
destruct (OTFacts.eq_dec (snd_ext b) (snd_ext e)).
elim H0. right. auto.
apply eq_refl.

destruct H7.
destruct H7. generalize (AE_weights _ _ H7). simpl. intro.
rewrite H8 in H7. left. auto.
generalize (IE_weights _ _ H7). simpl. congruence.

rewrite <-H5. rewrite H4. auto.

unfold redirect. destruct (OTFacts.eq_dec (fst_ext b) (snd_ext e)).
elim H0. left. auto.
destruct (OTFacts.eq_dec (snd_ext b) (snd_ext e)).
elim H0. right. auto.
apply eq_refl.

apply eq_ordered_eq. constructor; simpl; try split.
apply Regs.eq_refl.
apply Regs.eq_refl.
fold (get_weight b). rewrite <-H3. simpl. apply OptionN_as_OT.eq_refl.

apply IHl. intros. apply HH. right. auto.

unfold h'. unfold h. intros.
split; intros.
apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 (EdgeSet.remove_3 H3)).
apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 H3).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H3)).

apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 (EdgeSet.remove_3 H3)).
apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 H3).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H3)).

unfold h'. unfold h. intros.
apply RegRegProps.Equal_remove. auto.

(* last part !!!!!!! *)

unfold AE_merge_up.
set (f :=  (fun (y : VertexSet.elt) (s'' : EdgeSet.t) =>
      EdgeSet.add (fst_ext e, y, Some 0%N) s'')) in *.
set (diff1 := (VertexSet.diff (preference_adj (fst_ext e) (merge e g p q))
             (preference_adj (fst_ext e) g))) in *.
set (diff2 :=  (VertexSet.diff (preference_adj (fst_ext e) g)
                   (preference_adj (fst_ext e) (merge e g p q)))) in *.

set (pref := preference_adj (fst_ext e) (merge e g p q)) in *.
rewrite VertexSet.fold_1 in H1.
generalize VertexSet.elements_2. intro HH.
generalize (HH pref). clear HH. intro HH.
set (f' := fun a e => f e a) in *. induction (VertexSet.elements pref).
simpl in H1. elim (EdgeSet.empty_1 H1).

set (set := (not_incident_merge (snd_ext e)
              (not_incident_merge (fst_ext e) s diff2)
              (preference_adj (snd_ext e) g))) in *.
rewrite MEdgeFacts.fold_left_assoc in H1.
set (tmp := fold_left f' l EdgeSet.empty) in *.
unfold f' in H1. unfold f in H1.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H1).
fold (eq (fst_ext e, a, Some N0) b) in H2.
rewrite <-H2.
destruct (Props.In_dec a (preference_adj (fst_ext e) g)).
cut (EdgeSet.In b set). intro Hcut.
rewrite VertexSet.fold_1. fold f'.
assert (~InA Vertex.eq a (VertexSet.elements diff1)).
intro. generalize (VertexSet.elements_2 H3). intro H4.
unfold diff1 in H4. elim (VertexSet.diff_2 H4 i).
induction (VertexSet.elements diff1). simpl.
rewrite H2. assumption.
rewrite MEdgeFacts.fold_left_assoc.
set (tmp' := fold_left f' l0 set) in *.
unfold f'. unfold f.
destruct (Vertex.eq_dec a a0).
apply EdgeSet.add_1. apply eq_ordered_eq. constructor; simpl. split; intuition.
apply OptionN_as_OT.eq_refl.
apply EdgeSet.add_2.
apply IHl0. intro. elim H3. right. auto.

unfold f'. unfold f. intros.
apply RegRegProps.add_add.

unfold f'. unfold f. intros.
apply RegRegProps.Dec.F.add_m. apply eq_refl. auto.

unfold set. cut (EdgeSet.In b (not_incident_merge (fst_ext e) s diff2)). intro.
set (set' := (not_incident_merge (fst_ext e) s diff2)) in *.
unfold not_incident_merge.
set (h := (fun (y : VertexSet.elt) (s' : EdgeSet.t) =>
      EdgeSet.remove (snd_ext e, y, Some 0%N) s')) in *.
set (adjsnd := preference_adj (snd_ext e) g) in *.
rewrite VertexSet.fold_1.
set (h' := fun a e => h e a) in *.
induction (VertexSet.elements adjsnd). simpl. assumption.
rewrite MEdgeFacts.fold_left_assoc.
set (tmp' := fold_left h' l set') in *.
unfold h'. unfold h.
apply EdgeSet.remove_2.
intro. elim H0.
destruct (eq_charac _ _ H4); change_rewrite; destruct H5.
left. auto.
right. auto. assumption.

unfold h'. unfold h. intros.
split; intros.
apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 (EdgeSet.remove_3 H4)).
apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 H4).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H4)).

apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 (EdgeSet.remove_3 H4)).
apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 H4).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H4)).

unfold h'. unfold h. intros.
apply RegRegProps.Equal_remove. auto.

unfold not_incident_merge.
set (h := (fun (y : VertexSet.elt) (s' : EdgeSet.t) =>
      EdgeSet.remove (fst_ext e, y, Some 0%N) s')) in *.
rewrite VertexSet.fold_1.
set (h' := fun a e => h e a) in *.
generalize VertexSet.elements_2. intro.
generalize (H3 diff2). clear H3. intro HHH.
induction (VertexSet.elements diff2). simpl.
rewrite H. split.
unfold aff_edge. exists N0. rewrite <-H2. auto.
left. rewrite <-H2. 
apply (proj2 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap g))). assumption.
rewrite MEdgeFacts.fold_left_assoc.
set (tmp' := fold_left h' l0 s) in *.
unfold h'. unfold h.
apply EdgeSet.remove_2.
intro.
assert (Vertex.eq a a0).
destruct (Vertex.eq_dec a a0). intuition.
assert (eq (fst_ext e, a0, Some N0) b) by auto. generalize H4. clear H3 H4. intro H3.
rewrite <-H3 in H2. destruct (eq_charac _ _ H2); change_rewrite; destruct H4.
auto.
apply Vertex.eq_trans with (y := fst_ext e); auto.
assert (~VertexSet.In a diff2).
intro. unfold diff2 in H5. elim (VertexSet.diff_2 H5).
apply HH. left. intuition.
elim H5.
rewrite H4. apply HHH. left. intuition.
apply IHl0.
intros. apply HHH. right. auto.

unfold h'. unfold h. intros.
split; intros.
apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 (EdgeSet.remove_3 H3)).
apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 H3).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H3)).

apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 (EdgeSet.remove_3 H3)).
apply EdgeSet.remove_2.
intro H5. elim (EdgeSet.remove_1 H5 H3).
apply (EdgeSet.remove_3 (EdgeSet.remove_3 H3)).

unfold h'. unfold h. intros.
apply RegRegProps.Equal_remove. auto.

rewrite VertexSet.fold_1.
fold f'.
generalize VertexSet.elements_1. intro HHH.
generalize (HHH diff1 a). clear HHH. intro HHH.
assert (VertexSet.In a diff1). apply VertexSet.diff_3. apply HH. left. intuition.
assumption.
induction (VertexSet.elements diff1). simpl.
generalize (HHH H3). intro H4. inversion H4.
rewrite MEdgeFacts.fold_left_assoc.
set (tmp' := fold_left f' l0 set) in *.
unfold f'. unfold f.
destruct (Vertex.eq_dec a a0).
apply EdgeSet.add_1.
apply eq_ordered_eq. constructor; simpl; try split; intuition.
apply OptionN_as_OT.eq_refl.
apply EdgeSet.add_2. apply IHl0. intro.
generalize (HHH H4). intro H5. inversion H5; subst.
elim (n0 H7).
assumption.

unfold f'. unfold f. intros.
apply RegRegProps.add_add.

unfold f'. unfold f. intros.
apply RegRegProps.Dec.F.add_m. apply eq_refl. auto.

apply IHl.
assumption.
intros. apply HH. right. auto.

unfold f'. unfold f. intros.
apply RegRegProps.add_add.

unfold f'. unfold f. intros.
apply RegRegProps.Dec.F.add_m. apply eq_refl. auto.
Qed.

Lemma AE_aux_3 : forall e g s p q,
(forall a, EdgeSet.In a s <-> aff_edge a /\ In_graph_edge a g) ->
(forall b, EdgeSet.In b (AE (merge e g p q))
           <->
           (~incident b (snd_ext e) /\
           ((EdgeSet.In b s /\ ~Interfere (fst_ext b) (snd_ext b) (merge e g p q)) \/  
            EdgeSet.In b (VertexSet.fold 
                            (fun y s' => EdgeSet.add (fst_ext e, y, Some N0) s')
                            (preference_adj (fst_ext e) (merge e g p q))
                            EdgeSet.empty)))).

Proof.
intros e g s p q. generalize I. intro H.
split; intros.
generalize (proj1 (In_graph_aff_edge_in_AE _ _) H1). intro H3.
destruct H3 as [H3 H4].
assert (~incident b (snd_ext e)) as Hinc.
intro. destruct H2; elim (merge_1 e g p q); auto.
unfold In_graph. rewrite H2. apply (proj1 (In_graph_edge_in_ext _ _ H4)).
unfold In_graph. rewrite H2. apply (proj2 (In_graph_edge_in_ext _ _ H4)).

split.
assumption.

assert (get_weight b = Some N0) as Hw.
apply AE_weights with (g := merge e g p q). assumption.

clear H1.
generalize (merge_4 e _ g p q H4). intro H1.
destruct H1. destruct H1 as [H1 H2]. destruct H2 as [H2 HH2].
assert (aff_edge x) as Haffb.
unfold same_type in HH2. destruct HH2; destruct H5;[auto|congruence].

unfold redirect in H2.
destruct (OTFacts.eq_dec (fst_ext x) (snd_ext e)).
right.
unfold weak_eq in H2. change_rewrite. destruct H2; destruct H2.

set (f := (fun (y : VertexSet.elt) (s' : EdgeSet.t) =>
           EdgeSet.add (fst_ext e, y, Some 0%N) s')) in *.
set (set := preference_adj (fst_ext e) (merge e g p q)) in *.
rewrite VertexSet.fold_1. set (f' := fun a e => f e a) in *.
generalize VertexSet.elements_1. intro HH.
generalize (HH set (snd_ext x)). clear HH. intro HH.
induction (VertexSet.elements set). simpl.
assert (InA Vertex.eq (snd_ext x) nil).
apply HH.
unfold set. rewrite <-H5. rewrite (compat_preference_adj _ _ _ (Vertex.eq_sym H2)).
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap_merge_map e g q p))).
cut (eq b (fst_ext b, snd_ext b, Some N0)). intro Heq.
rewrite <-Heq. destruct H4. assumption.
generalize (IE_weights _ _ H4). congruence.
rewrite (edge_eq b); change_rewrite.
assert (get_weight b = Some N0).
apply AE_weights with (g:= merge e g p q). rewrite In_graph_aff_edge_in_AE.
split; auto.
rewrite H6. apply eq_refl.
inversion H6.

rewrite MEdgeFacts.fold_left_assoc.
set (tmp := fold_left f' l EdgeSet.empty) in *.
unfold f'. unfold f.
destruct (Vertex.eq_dec (snd_ext x) a).
apply EdgeSet.add_1.
apply eq_ordered_eq.
rewrite (edge_eq b).
constructor; simpl. split; intuition.
rewrite <-e0. intuition.
assert (get_weight b = Some N0).
apply AE_weights with (g:= merge e g p q). rewrite In_graph_aff_edge_in_AE.
split; intuition.
rewrite H6. apply OptionN_as_OT.eq_refl.
apply EdgeSet.add_2.
apply IHl. intro. generalize (HH H6). intro H7.
inversion H7; subst.
elim (n H9).
auto.

unfold f'. unfold f. intros.
apply RegRegProps.add_add.

unfold f'. unfold f. intros.
apply RegRegProps.Dec.F.add_m. apply eq_refl. auto.

set (f := (fun (y : VertexSet.elt) (s' : EdgeSet.t) =>
           EdgeSet.add (fst_ext e, y, Some 0%N) s')) in *.
set (set := preference_adj (fst_ext e) (merge e g p q)) in *.
rewrite VertexSet.fold_1. set (f' := fun a e => f e a) in *.
generalize VertexSet.elements_1. intro HH.
generalize (HH set (snd_ext x)). clear HH. intro HH.
induction (VertexSet.elements set). simpl.
assert (InA Vertex.eq (snd_ext x) nil).
apply HH.
unfold set. rewrite <-H2. rewrite (compat_preference_adj _ _ _ (Vertex.eq_sym H5)).
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap_merge_map e g q p))).
cut (eq b (snd_ext b, fst_ext b, Some N0)). intro Heq.
rewrite <-Heq. destruct H4. assumption.
generalize (IE_weights _ _ H4). congruence.
rewrite (edge_eq b); change_rewrite.
assert (get_weight b = Some N0).
apply AE_weights with (g:= merge e g p q). rewrite In_graph_aff_edge_in_AE.
split; auto.
rewrite H6. apply edge_comm.
inversion H6.

rewrite MEdgeFacts.fold_left_assoc.
set (tmp := fold_left f' l EdgeSet.empty) in *.
unfold f'. unfold f.
destruct (Vertex.eq_dec (snd_ext x) a).
apply EdgeSet.add_1.
fold (eq (fst_ext e, a, Some N0) b).
rewrite edge_comm. apply eq_ordered_eq.
rewrite (edge_eq b).
constructor; simpl. split; intuition.
rewrite <-e0. intuition.
assert (get_weight b = Some N0).
apply AE_weights with (g:= merge e g p q). rewrite In_graph_aff_edge_in_AE.
split; auto.
rewrite H6. apply OptionN_as_OT.eq_refl.
apply EdgeSet.add_2.
apply IHl. intro. generalize (HH H6). intro H7.
inversion H7; subst.
elim (n H9).
auto.

unfold f'. unfold f. intros.
apply RegRegProps.add_add.

unfold f'. unfold f. intros.
apply RegRegProps.Dec.F.add_m. apply eq_refl. auto.

destruct (OTFacts.eq_dec (snd_ext x) (snd_ext e)).

right.
unfold weak_eq in H2. change_rewrite. destruct H2; destruct H2.
assert (get_weight x = Some N0).
apply AE_weights with (g:=g). apply (proj2 (In_graph_aff_edge_in_AE _ _)).
split; auto.

set (f := (fun (y : VertexSet.elt) (s' : EdgeSet.t) =>
           EdgeSet.add (fst_ext e, y, Some 0%N) s')) in *.
set (set := preference_adj (fst_ext e) (merge e g p q)) in *.
rewrite VertexSet.fold_1. set (f' := fun a e => f e a) in *.
generalize VertexSet.elements_1. intro HH.
generalize (HH set (fst_ext x)). clear HH. intro HH.
induction (VertexSet.elements set). simpl.
assert (InA Vertex.eq (fst_ext x) nil).
apply HH.
unfold set. rewrite <-H2. rewrite (compat_preference_adj _ _ _ (Vertex.eq_sym H5)).
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap_merge_map e g q p))).
cut (eq b (snd_ext b, fst_ext b, Some N0)). intro Heq.
rewrite <-Heq. destruct H4. assumption.
generalize (IE_weights _ _ H4). congruence.
rewrite (edge_eq b); change_rewrite.
assert (get_weight b = Some N0).
apply AE_weights with (g:= merge e g p q). rewrite In_graph_aff_edge_in_AE.
split; auto.
rewrite H7. apply edge_comm.
inversion H7.

rewrite MEdgeFacts.fold_left_assoc.
set (tmp := fold_left f' l EdgeSet.empty) in *.
unfold f'. unfold f.
destruct (Vertex.eq_dec (fst_ext x) a).
apply EdgeSet.add_1.
fold (eq (fst_ext e, a, Some N0) b).
rewrite edge_comm. apply eq_ordered_eq.
rewrite (edge_eq b).
constructor; simpl. split; intuition.
rewrite <-e0. intuition.
rewrite Hw. auto. apply OptionN_as_OT.eq_refl.
apply EdgeSet.add_2.
apply IHl. intro. generalize (HH H7). intro H8.
inversion H8; subst.
elim (n0 H10).
auto.

unfold f'. unfold f. intros.
apply RegRegProps.add_add.

unfold f'. unfold f. intros.
apply RegRegProps.Dec.F.add_m. apply eq_refl. auto.

set (f := (fun (y : VertexSet.elt) (s' : EdgeSet.t) =>
           EdgeSet.add (fst_ext e, y, Some 0%N) s')) in *.
set (set := preference_adj (fst_ext e) (merge e g p q)) in *.
rewrite VertexSet.fold_1. set (f' := fun a e => f e a) in *.
generalize VertexSet.elements_1. intro HH.
generalize (HH set (fst_ext x)). clear HH. intro HH.
induction (VertexSet.elements set). simpl.
assert (InA Vertex.eq (fst_ext x) nil).
apply HH.
unfold set. rewrite <-H5. rewrite (compat_preference_adj _ _ _ (Vertex.eq_sym H2)).
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap_merge_map e g q p))).
cut (eq b (fst_ext b, snd_ext b, Some N0)). intro Heq.
rewrite <-Heq. destruct H4. assumption.
generalize (IE_weights _ _ H4). congruence.
rewrite (edge_eq b); change_rewrite.
assert (get_weight b = Some N0).
apply AE_weights with (g:= merge e g p q). rewrite In_graph_aff_edge_in_AE.
split; auto.
rewrite H6. apply eq_refl.
inversion H6.

rewrite MEdgeFacts.fold_left_assoc.
set (tmp := fold_left f' l EdgeSet.empty) in *.
unfold f'. unfold f.
destruct (Vertex.eq_dec (fst_ext x) a).
apply EdgeSet.add_1.
apply eq_ordered_eq.
rewrite (edge_eq b).
constructor; simpl. split; intuition.
rewrite H5. intuition.
rewrite Hw. apply OptionN_as_OT.eq_refl.
apply EdgeSet.add_2.
apply IHl. intro. generalize (HH H6). intro H7.
inversion H7; subst.
elim (n0 H9).
auto.

unfold f'. unfold f. intros.
apply RegRegProps.add_add.

unfold f'. unfold f. intros.
apply RegRegProps.Dec.F.add_m. apply eq_refl. auto.

assert (eq b x) as Heq.
unfold weak_eq in H2. destruct H2; destruct H2.
apply eq_ordered_eq. constructor; simpl.
inversion H2; auto.
fold (get_weight b). fold (get_weight x).
rewrite Hw.
assert (get_weight x = Some N0).
apply AE_weights with (g:=g).
rewrite In_graph_aff_edge_in_AE.
split; auto.
rewrite H6. apply OptionN_as_OT.eq_refl.
rewrite (edge_eq b). rewrite (edge_eq x).
rewrite edge_comm. apply eq_ordered_eq. constructor; simpl.
inversion H2; simpl in *; intuition.
rewrite H6. rewrite H7. auto.
rewrite H6. rewrite H7. auto.
assert (get_weight x = Some N0).
apply AE_weights with (g:=g).
rewrite In_graph_aff_edge_in_AE.
split; intuition.
rewrite H6. rewrite Hw. apply OptionN_as_OT.eq_refl.
left. split.
rewrite Heq.
rewrite (H0 x). split.
exists N0. rewrite <-Heq. auto. auto.
intro. elim (simple_graph (merge e g p q) (fst_ext b) (snd_ext b)).
split.
unfold Interfere in H5.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ None (sym_imap_merge_map e g q p))).
rewrite edge_comm.
destruct H5.
generalize (AE_weights _ _ H5). simpl. congruence.
assumption.
apply (proj1 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap_merge_map e g q p))).
rewrite edge_comm.
cut (eq (fst_ext b, snd_ext b, Some N0) b). intro Heq2.
rewrite Heq2.
destruct H4.
assumption.
generalize (IE_weights _ _ H4). congruence.
rewrite (edge_eq b). change_rewrite. rewrite Hw. apply eq_refl.

(* second part !!! *)

destruct H1.
cut (get_weight b = Some N0). intro Hw.
assert (eq b (fst_ext b, snd_ext b, Some N0)).
rewrite (edge_eq b); change_rewrite.
apply eq_ordered_eq. constructor; simpl.
split; intuition.
rewrite Hw. apply OptionN_as_OT.eq_refl.

destruct H2.
rewrite H3.
rewrite In_graph_aff_edge_in_AE. split.
exists N0; simpl; auto.
cut (eq b (redirect (snd_ext e) (fst_ext e) b)). intro Hcut.
rewrite <-H3. rewrite Hcut. rewrite (edge_eq _).
cut (get_weight (redirect (snd_ext e) (fst_ext e) b) = Some N0). intro Hw'.
cut (Prefere (fst_ext (redirect (snd_ext e) (fst_ext e) b))
                    (snd_ext (redirect (snd_ext e) (fst_ext e) b))
                    (merge e g p q)). intro.
unfold Prefere in H4. destruct H4.
assert (get_weight ((fst_ext (redirect (snd_ext e) (fst_ext e) b),
                                snd_ext (redirect (snd_ext e) (fst_ext e) b), Some x)) = Some N0).
apply (AE_weights) with (g:=merge e g p q).
rewrite In_graph_aff_edge_in_AE. split.
exists x. auto. auto.
rewrite Hw'. rewrite <-H5. simpl. auto.
destruct H2. apply merge_5.
apply (proj1 (H0 _) H2).
intro. elim H1.
destruct (eq_charac _ _ H5). right; intuition. left; intuition.
exists N0; simpl; auto.
intro. unfold Interfere in H5.
cut (eq (fst_ext (redirect (snd_ext e) (fst_ext e) b),
         snd_ext (redirect (snd_ext e) (fst_ext e) b),
         None)
         (fst_ext b, snd_ext b, None)). intro H6.
rewrite H6 in H5.
elim H4. unfold Interfere. assumption.
unfold redirect; change_rewrite.
destruct (OTFacts.eq_dec (fst_ext b) (snd_ext e)).
elim H1. left. auto.
destruct (OTFacts.eq_dec (snd_ext b) (snd_ext e)).
elim H1. right. auto.
apply eq_refl.
rewrite <-Hcut. assumption.
unfold redirect; change_rewrite.
destruct (OTFacts.eq_dec (fst_ext b) (snd_ext e)).
elim H1. left. auto.
destruct (OTFacts.eq_dec (snd_ext b) (snd_ext e)).
elim H1. right. auto.
apply eq_refl.

rewrite H3.
apply (proj2 (edgemap_to_edgeset_charac _ _ _ (Some N0) (sym_pmap_merge_map e g q p))).
set (f :=  (fun (y : VertexSet.elt) (s' : EdgeSet.t) =>
           EdgeSet.add (fst_ext e, y, Some 0%N) s')) in *.
set (s' := preference_adj (fst_ext e) (merge e g p q)) in *.
rewrite VertexSet.fold_1 in H2.
generalize VertexSet.elements_2. intro HH.
generalize (HH s'). clear HH. intro HH.
induction (VertexSet.elements s'). simpl in H2.
elim (EdgeSet.empty_1 H2).
set (f' := fun a e => f e a) in *.
rewrite MEdgeFacts.fold_left_assoc in H2.
set (tmp := fold_left f' l EdgeSet.empty) in *.
unfold f' in H2. unfold f in H2.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H2).
fold (eq (fst_ext e, a, Some N0) b) in H4.
rewrite (edge_eq b) in H4.
destruct (eq_charac _ _ H4); change_rewrite.
destruct H5.
assert (VertexSet.In (snd_ext b) s').
apply HH. left. intuition.
unfold s' in H7.
unfold adj_set. rewrite (MapFacts.find_o _ (Vertex.eq_sym H5)).
assumption.
destruct H5.
assert (VertexSet.In (fst_ext b) s').
apply HH. left. intuition.
unfold s' in H7.
unfold preference_adj in H7. unfold adj_set in H7. rewrite (MapFacts.find_o _ H5) in H7.
apply (sym_pmap_merge_map e g q p). assumption.
apply IHl.
assumption.
intros. apply HH. right. auto.

unfold f'. unfold f. intros.
apply RegRegProps.add_add.

unfold f'. unfold f. intros.
apply RegRegProps.Dec.F.add_m. apply eq_refl. auto.

destruct H2.
rewrite AE_weights with (g:=g). auto.
rewrite (In_graph_aff_edge_in_AE). rewrite <-H0. intuition.
set (f := (fun (y : VertexSet.elt) (s' : EdgeSet.t) =>
           EdgeSet.add (fst_ext e, y, Some 0%N) s')) in *.
set (s' := (preference_adj (fst_ext e) (merge e g p q))) in *.
rewrite VertexSet.fold_1 in H2.
set (f' := fun a e => f e a) in *.
induction (VertexSet.elements s'). simpl in H2.
elim (EdgeSet.empty_1 H2).
rewrite MEdgeFacts.fold_left_assoc in H2.
set (tmp := fold_left f' l EdgeSet.empty) in *.
unfold f' in H2. unfold f in H2.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H2).
fold (eq (fst_ext e, a, Some N0) b) in H3. rewrite <-H3.
auto.
apply IHl. assumption.

unfold f'. unfold f. intros.
apply RegRegProps.add_add.

unfold f'. unfold f. intros.
apply RegRegProps.Dec.F.add_m. apply eq_refl. auto.
Qed.

Lemma AE_merge_wl_aux : forall e g s p q,
(forall a, EdgeSet.In a s <-> aff_edge a /\ In_graph_edge a g) ->
(EdgeSet.Equal  (AE_merge_up (preference_adj (fst_ext e) (merge e g p q))
                             (preference_adj (fst_ext e) g)
                             (preference_adj (snd_ext e) g)
                             e s)
                (AE (merge e g p q))).

Proof.
intros.
unfold EdgeSet.Equal. intro. rewrite (AE_aux_2 e g s p q H).
                             rewrite (AE_aux_3 e g s p q H).
reflexivity.
Qed.

Lemma AE_merge_wl : forall e g s p q,
(forall a, EdgeSet.In a s <-> aff_edge a /\ In_graph_edge a g) ->
(forall b, EdgeSet.In b (AE_merge_up (preference_adj (fst_ext e) (merge e g p q))
                                     (preference_adj (fst_ext e) g)
                                     (preference_adj (snd_ext e) g)
                                     e s)
           <->
           aff_edge b /\ In_graph_edge b (merge e g p q)).

Proof.
intros.
rewrite <-(In_graph_aff_edge_in_AE).
apply AE_merge_wl_aux; assumption.
Qed.

(* It implements the interface *)

(* Specification of the interference neighborhood *)
Lemma in_interf : forall x y g,
VertexSet.In x (interference_adj y g) <-> In_graph_edge (x,y,None) g.

Proof.
split; intros.
apply in_interf_interf. auto.
apply interf_in_interf. auto.
Qed.

(* Specification of the preference neighborhood *)
Lemma in_pref : forall x y g,
VertexSet.In x (preference_adj y g) <-> exists w, In_graph_edge (x,y,Some w) g.

Proof.
split; intros.
apply in_pref_pref. auto.
destruct H. apply pref_in_pref with (w:=x0). auto.
Qed.
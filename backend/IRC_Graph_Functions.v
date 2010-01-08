Require Import FSets.
Require Import InterfGraphMapImp.
Require Import Spill_WL.
Require Import ZArith.
Require Import Simplify_WL.
Require Import Spill_WL.
Require Import Merge_WL.
Require Import Freeze_WL.
Require Import IRC_graph.
Require Import Edges.
Require Import Conservative_criteria.
Require Import WS.

Import RegFacts Props OTFacts.

Definition any_vertex := VertexSet.choose.

(* simplify *)

Definition simplify_irc r ircg H :=
Make_IRC_Graph (remove_vertex r (irc_g ircg))
               (simplify_wl r ircg (irc_k ircg)) 
               (pal ircg)
               (irc_k ircg)
               (WS_simplify r ircg H)
               (Hk ircg).

Definition simplify g : option (Register.t * irc_graph) :=
let simplifyWL := get_simplifyWL (irc_wl g) in
match any_vertex simplifyWL as v return (any_vertex simplifyWL = v -> option (Register.t * irc_graph)) with
|Some r => fun H : any_vertex simplifyWL = Some r =>
           Some (r, simplify_irc r g (VertexSet.choose_1 H))
|None => fun H : any_vertex simplifyWL = None => None
end (refl_equal (any_vertex simplifyWL)).

Lemma simplify_inv_aux :
  forall g P,
    match simplify g with
    | Some x =>
         forall ( H : (any_vertex (get_simplifyWL (irc_wl g)) = Some (fst x))),
         (simplify_irc (fst x) g (VertexSet.choose_1 H) = snd x) -> P
    | None =>
         (any_vertex (get_simplifyWL (irc_wl g)) = None -> P)
    end -> P.
Proof.
  intros g P.
  unfold simplify.

  set (simplifyWL := get_simplifyWL (irc_wl g)) in *.
  set (Z := any_vertex simplifyWL) in *.

  refine
    (match Z as W
     return forall (H : Z = W),

match
  match W as v return (Z = v -> option (Register.t * irc_graph)) with
  | Some r =>
      fun H : Z = Some r => Some (r, simplify_irc r g (VertexSet.choose_1 H))
  | None => fun _ : Z = None => None
  end H
with
| Some x => forall H : Z = Some (fst x), simplify_irc (fst x) g (VertexSet.choose_1 H) = snd x -> P
| None => Z = None -> P
end -> P
  
     with
       | Some x => _
       | None => _
     end _).

simpl. intros. apply X with (H0 := H). reflexivity.
auto.
Qed.  

Lemma simplify_inv : forall g res,
simplify g = Some res ->
any_vertex (get_simplifyWL (irc_wl g)) = Some (fst res).
Proof.
  intros.
  apply simplify_inv_aux with g.
  rewrite H.
  auto.
Qed.

Lemma simplify_inv2 : forall g res,
simplify g = Some res ->
exists H, snd res = simplify_irc (fst res) g (VertexSet.choose_1 H).

Proof.
intros.
apply (simplify_inv_aux g). rewrite H.
simpl. intros. rewrite <-H1.
exists H0. reflexivity.
Qed.

(* merge *)

Definition merge_irc e ircg pin paff :=
let g' := merge e (irc_g ircg) pin paff in
Make_IRC_Graph g' 
              (merge_wl3 e ircg g' pin paff) 
              (pal ircg) 
              (irc_k ircg)
              (WS_coalesce _ _ pin paff)
              (Hk ircg).

Definition coalesce g : option (Edge.t * irc_graph) :=
let movesWL := get_movesWL (irc_wl g) in
let graph := irc_g g in
let HWS := HWS_irc g in
let k := irc_k g in
match any_coalescible_edge movesWL graph k as e 
return (any_coalescible_edge movesWL graph k = e -> option (Edge.t * irc_graph)) with
|Some edge => fun H : any_coalescible_edge movesWL graph k = Some edge =>
              let Hin := any_coalescible_edge_11 _ _ _ _ H in
              let Hing := proj2 (In_move_props _ _ _ _ _ _ _ _ Hin (refl_equal _) HWS) in
              let Haff := proj1 (In_move_props _ _ _ _ _ _ _ _ Hin (refl_equal _) HWS) in
              Some (edge,merge_irc edge g Hing Haff)
|None => fun H : any_coalescible_edge movesWL graph k = None => None
end (refl_equal (any_coalescible_edge movesWL graph k)).

Lemma coalesce_inv_aux :
  forall g P,
    match coalesce g with
    | Some x =>
         forall (H : (any_coalescible_edge (get_movesWL (irc_wl g)) (irc_g g) (irc_k g) = Some (fst x))),
         (merge_irc (fst x) g 
         (proj2 (In_move_props _ _ _ _ _ _ _ _ (any_coalescible_edge_11 _ _ _ _ H) (refl_equal _) (HWS_irc g)))
         (proj1 (In_move_props _ _ _ _ _ _ _ _ (any_coalescible_edge_11 _ _ _ _ H) (refl_equal _) (HWS_irc g))))
         = snd x -> P
    | None =>
         (any_coalescible_edge (get_movesWL (irc_wl g)) (irc_g g) (irc_k g) = None -> P)
    end -> P.
Proof.
  intros g P.
  unfold coalesce.

  set (movesWL := get_movesWL (irc_wl g)) in *.
  set (Z := any_coalescible_edge movesWL (irc_g g) (irc_k g)) in *.

  refine
    (match Z as W
     return forall (H : Z = W),

match
  match W as e return (Z = e -> option (Edge.t * irc_graph)) with
  | Some edge =>
      fun H : Z = Some edge => Some (edge,
merge_irc edge g
          (proj2
             (In_move_props edge (irc_g g)
                (get_spillWL (irc_wl g), get_freezeWL (irc_wl g),
                get_simplifyWL (irc_wl g), movesWL) movesWL
                (get_spillWL (irc_wl g)) (get_freezeWL (irc_wl g))
                (get_simplifyWL (irc_wl g)) (irc_k g)
                (any_coalescible_edge_11 edge (irc_g g) (irc_k g) movesWL H)
                (refl_equal
                   (get_spillWL (irc_wl g), get_freezeWL (irc_wl g),
                   get_simplifyWL (irc_wl g), movesWL)) (HWS_irc g)))
          (proj1
             (In_move_props edge (irc_g g)
                (get_spillWL (irc_wl g), get_freezeWL (irc_wl g),
                get_simplifyWL (irc_wl g), movesWL) movesWL
                (get_spillWL (irc_wl g)) (get_freezeWL (irc_wl g))
                (get_simplifyWL (irc_wl g)) (irc_k g)
                (any_coalescible_edge_11 edge (irc_g g) (irc_k g) movesWL H)
                (refl_equal
                   (get_spillWL (irc_wl g), get_freezeWL (irc_wl g),
                   get_simplifyWL (irc_wl g), movesWL)) (HWS_irc g))))
  | None => fun _ : Z = None => None
  end H
with
| Some x =>
    forall H : Z = Some (fst x),
    merge_irc (fst x) g
      (proj2
         (In_move_props (fst x) (irc_g g)
            (get_spillWL (irc_wl g), get_freezeWL (irc_wl g),
            get_simplifyWL (irc_wl g), movesWL) movesWL
            (get_spillWL (irc_wl g)) (get_freezeWL (irc_wl g))
            (get_simplifyWL (irc_wl g)) (irc_k g)
            (any_coalescible_edge_11 (fst x) (irc_g g) (irc_k g) movesWL H)
            (refl_equal
               (get_spillWL (irc_wl g), get_freezeWL (irc_wl g),
               get_simplifyWL (irc_wl g), movesWL)) (HWS_irc g)))
      (proj1
         (In_move_props (fst x) (irc_g g)
            (get_spillWL (irc_wl g), get_freezeWL (irc_wl g),
            get_simplifyWL (irc_wl g), movesWL) movesWL
            (get_spillWL (irc_wl g)) (get_freezeWL (irc_wl g))
            (get_simplifyWL (irc_wl g)) (irc_k g)
            (any_coalescible_edge_11 (fst x) (irc_g g) (irc_k g) movesWL H)
            (refl_equal
               (get_spillWL (irc_wl g), get_freezeWL (irc_wl g),
               get_simplifyWL (irc_wl g), movesWL)) (HWS_irc g))) = snd x ->
    P
| None => Z = None -> P
end -> P  
     with
       | Some x => _
       | None => _
     end _).

simpl. intros. apply X with (H0 := H). reflexivity.
auto.
Qed.  

Lemma coalesce_inv : forall g res,
coalesce g = Some res ->
any_coalescible_edge (get_movesWL (irc_wl g)) (irc_g g) (irc_k g) = Some (fst res).
Proof.
  intros.
  apply (coalesce_inv_aux g).
  rewrite H.
  auto.
Qed.

Lemma coalesce_inv_2 : forall g res,
coalesce g = Some res ->
exists H, exists H', snd res = merge_irc (fst res) g H H'.

Proof.
intros.
apply (coalesce_inv_aux g).
rewrite H.
simpl. intros.
exists ((proj2
          (In_move_props (fst res) (irc_g g)
             (get_spillWL (irc_wl g), get_freezeWL (irc_wl g),
             get_simplifyWL (irc_wl g), get_movesWL (irc_wl g))
             (get_movesWL (irc_wl g)) (get_spillWL (irc_wl g))
             (get_freezeWL (irc_wl g)) (get_simplifyWL (irc_wl g))
             (irc_k g)
             (any_coalescible_edge_11 (fst res) (irc_g g) (irc_k g)
                (get_movesWL (irc_wl g)) H0)
             (refl_equal
                (get_spillWL (irc_wl g), get_freezeWL (irc_wl g),
                get_simplifyWL (irc_wl g), get_movesWL (irc_wl g)))
             (HWS_irc g)))).
exists ((proj1
          (In_move_props (fst res) (irc_g g)
             (get_spillWL (irc_wl g), get_freezeWL (irc_wl g),
             get_simplifyWL (irc_wl g), get_movesWL (irc_wl g))
             (get_movesWL (irc_wl g)) (get_spillWL (irc_wl g))
             (get_freezeWL (irc_wl g)) (get_simplifyWL (irc_wl g))
             (irc_k g)
             (any_coalescible_edge_11 (fst res) (irc_g g) (irc_k g)
                (get_movesWL (irc_wl g)) H0)
             (refl_equal
                (get_spillWL (irc_wl g), get_freezeWL (irc_wl g),
                get_simplifyWL (irc_wl g), get_movesWL (irc_wl g)))
             (HWS_irc g)))).
auto.
Qed.

(* freeze *)

Definition delete_preference_edges_irc2 v ircg Hing Hdep :=
let k := irc_k ircg in
let g' := delete_preference_edges v (irc_g ircg) Hing in
Make_IRC_Graph g' 
               (delete_preferences_wl2 v ircg k) 
               (pal ircg)
               (irc_k ircg)
               (WS_freeze v ircg Hing Hdep)
               (Hk ircg).

Definition freeze g : option (Register.t * irc_graph) :=
let freezeWL := get_freezeWL (irc_wl g) in
let graph := irc_g g in
let HWS := HWS_irc g in
match any_vertex freezeWL as r
return (any_vertex freezeWL = r -> option (Register.t*irc_graph)) with
|Some x => fun H : any_vertex freezeWL = Some x =>
           let Hin := VertexSet.choose_1 H in
           let Hing := proj1 (proj2 (proj2 (In_freeze_props _ _ _ _ _ _ _ _ Hin (refl_equal _) HWS)))in
           Some (x,delete_preference_edges_irc2 x g Hing Hin)
|None => fun H : any_vertex freezeWL = None => None
end (refl_equal (any_vertex freezeWL)).

Lemma freeze_inv_aux :
  forall g P,
    match freeze g with
    | Some x =>
         forall ( H : (any_vertex (get_freezeWL (irc_wl g)) = Some (fst x))),
         (delete_preference_edges_irc2 (fst x) g 
         (proj1 (proj2 (proj2 (In_freeze_props _ _ _ _ _ _ _ _ (VertexSet.choose_1 H) (refl_equal _) (HWS_irc g)))))
         (VertexSet.choose_1 H) = snd x) -> P
    | None =>
         (any_vertex (get_freezeWL (irc_wl g)) = None -> P)
    end -> P.

Proof.
  intros g P.
  unfold freeze.

  set (freezeWL := get_freezeWL (irc_wl g)) in *.
  set (Z := any_vertex freezeWL) in *.

  refine
    (match Z as W
     return forall (H : Z = W),

match
  match W as v return (Z = v -> option (Register.t * irc_graph)) with
  | Some x =>
      fun H : Z = Some x => Some
        (x,
        delete_preference_edges_irc2 x g
          (proj1
             (proj2
                (proj2
                   (In_freeze_props x (irc_g g)
                      (get_spillWL (irc_wl g), freezeWL,
                      get_simplifyWL (irc_wl g), get_movesWL (irc_wl g))
                      freezeWL (get_spillWL (irc_wl g))
                      (get_simplifyWL (irc_wl g)) (get_movesWL (irc_wl g))
                      (irc_k g) (VertexSet.choose_1 H)
                      (refl_equal
                         (get_spillWL (irc_wl g), freezeWL,
                         get_simplifyWL (irc_wl g), get_movesWL (irc_wl g)))
                      (HWS_irc g))))) (VertexSet.choose_1 H))
  | None => fun _ : Z = None => None
  end H
with
| Some x => 

forall H : Z = Some (fst x),
    delete_preference_edges_irc2 (fst x) g
      (proj1
         (proj2
            (proj2
               (In_freeze_props (fst x) (irc_g g)
                  (get_spillWL (irc_wl g), freezeWL,
                  get_simplifyWL (irc_wl g), get_movesWL (irc_wl g)) freezeWL
                  (get_spillWL (irc_wl g)) (get_simplifyWL (irc_wl g))
                  (get_movesWL (irc_wl g)) (irc_k g)
                  (VertexSet.choose_1 H)
                  (refl_equal
                     (get_spillWL (irc_wl g), freezeWL,
                     get_simplifyWL (irc_wl g), get_movesWL (irc_wl g)))
                  (HWS_irc g))))) (VertexSet.choose_1 H) = snd x -> P
| None => Z = None -> P
end -> P
     with
       | Some x => _
       | None => _
     end _).

simpl. intros. apply X with (H0 := H). reflexivity.
auto.
Qed.

Lemma freeze_inv : forall g res,
freeze g = Some res ->
any_vertex (get_freezeWL (irc_wl g)) = Some (fst res).
Proof.
  intros.
  apply freeze_inv_aux with g.
  rewrite H.
  auto.
Qed.

Lemma freeze_inv2 : forall g res,
freeze g = Some res ->
exists H', exists H, snd res = delete_preference_edges_irc2 (fst res) g H H'.

Proof.
intros.
apply (freeze_inv_aux g). rewrite H.
simpl. intros. rewrite <-H1.
exists (VertexSet.choose_1 H0).
exists (proj1 (proj2 (proj2 (In_freeze_props _ _ _ _ _ _ _ _ (VertexSet.choose_1 H0) (refl_equal _) (HWS_irc g))))). reflexivity.
Qed.

(* spill *)
Definition spill_irc r ircg H :=
Make_IRC_Graph (remove_vertex r (irc_g ircg))
               (spill_wl r ircg (irc_k ircg)) 
               (pal ircg)
               (irc_k ircg)
               (WS_spill r ircg H)
               (Hk ircg).

Definition cost_order (opt : (Register.t*nat*nat)) y g :=
let (tmp, pref_card) := opt in
let (x, int_card) := tmp in
let y_int := VertexSet.cardinal (interference_adj y g) in
match lt_eq_lt_dec y_int int_card with
|inleft (left _) => opt
|inleft (right _) => let y_pref := VertexSet.cardinal (preference_adj y g) in
                              match le_lt_dec pref_card y_pref with
                     |left _ => opt
                     |right _ => (y, y_int, y_pref)
                     end
|inright _ => (y, y_int, VertexSet.cardinal (preference_adj y g))
end.

Definition lowest_cost_aux s g o :=
VertexSet.fold (fun v o => match o with
                         | Some opt => Some (cost_order opt v g)
                         | None => Some (v, VertexSet.cardinal (interference_adj v g),
                                                         VertexSet.cardinal (preference_adj v g))
                         end)
             s
             o.

Definition lowest_cost s g := 
match lowest_cost_aux s g None with
| Some r => Some (fst (fst r))
| None => None
end.

Lemma lowest_cost_aux_in : forall x s g o,
lowest_cost_aux s g o = Some x->
VertexSet.In (fst (fst x)) s \/ o = Some x.

Proof.
intros. unfold lowest_cost_aux in H.
set (f :=  (fun (v : VertexSet.elt) (o : option (MyRegisters.Regs.t * nat * nat)) =>
       match o with
       | Some opt => Some (cost_order opt v g)
       | None =>
           Some
             (v, VertexSet.cardinal (interference_adj v g),
             VertexSet.cardinal (preference_adj v g))
       end )) in *.
unfold VertexSet.elt in *.
fold f in H.
rewrite VertexSet.fold_1 in H.
set (f' := fun a e => f e a) in *.
unfold VertexSet.elt in *. fold f' in H.
generalize VertexSet.elements_2. intro HH.
generalize (HH s). clear HH. intro HH.
generalize x o H. clear H. 
induction (VertexSet.elements s). intros x0 o0 H.
simpl in H. right. auto.
simpl. intros.
assert (VertexSet.In (fst (fst x0)) s \/ (f' o0 a) = Some x0).
apply IHl.
intros. apply HH. right. auto.
auto.
destruct H0.
left. auto.
unfold f' in H0. unfold f in H0.
case_eq o0; intros.
rewrite H1 in *.
case_eq (cost_order p a g); intros.
rewrite H2 in H0. unfold cost_order in H2.
destruct p. simpl in *. destruct p. simpl in *.
destruct (lt_eq_lt_dec (VertexSet.cardinal (interference_adj a g)) n1). destruct s0.
right. rewrite H2. auto.
destruct (le_lt_dec n0 (VertexSet.cardinal (preference_adj a g))).
right. rewrite H2. auto.
left. apply HH. left. destruct p0. simpl in *.
destruct x0. destruct p. simpl in *.
inversion H0. inversion H2. subst. intuition.
left. apply HH. left. destruct p0. simpl in *.
destruct x0. destruct p. simpl in *.
inversion H0. inversion H2. subst. intuition.
rewrite H1 in H0.
unfold f' in H. rewrite H1 in H. simpl in H. rewrite H0 in H.
fold f' in H.
left. apply HH. inversion H0. simpl. left. intuition.
Qed.

Lemma lowest_cost_in : forall x s g,
lowest_cost s g = Some x ->
VertexSet.In x s.

Proof.
intros. unfold lowest_cost in H. 
case_eq (lowest_cost_aux s g None); intros; rewrite H0 in H.
generalize (lowest_cost_aux_in p s g None H0). intro.
destruct H1. inversion H. subst. auto.
congruence.
congruence.
Qed.

Definition spill g : option (Register.t * irc_graph) :=
let spillWL := get_spillWL (irc_wl g) in
match lowest_cost spillWL (irc_g g) as v return (lowest_cost spillWL (irc_g g) = v -> option (Register.t * irc_graph)) with
|Some r => fun H : lowest_cost spillWL (irc_g g) = Some r =>
           Some (r, spill_irc r g (lowest_cost_in _ _ _ H))
|None => fun H : lowest_cost spillWL (irc_g g) = None => None
end (refl_equal (lowest_cost spillWL (irc_g g))).

Lemma spill_inv_aux :
  forall g P,
    match spill g with
    | Some x =>
         forall ( H : (lowest_cost (get_spillWL (irc_wl g)) (irc_g g) = Some (fst x))),
         (spill_irc (fst x) g (lowest_cost_in _ _ _ H) = snd x) -> P
    | None =>
         (lowest_cost (get_spillWL (irc_wl g)) (irc_g g) = None -> P)
    end -> P.
Proof.
  intros g P.
  unfold spill.

  set (spillWL := get_spillWL (irc_wl g)) in *.
  set (Z := lowest_cost spillWL (irc_g g)) in *.

  refine
    (match Z as W
     return forall (H : Z = W),

match
  match W as v return (Z = v -> option (Register.t * irc_graph)) with
  | Some r =>
      fun H : Z = Some r => Some (r, spill_irc r g (lowest_cost_in _ _ _ H))
  | None => fun _ : Z = None => None
  end H
with
| Some x => forall H : Z = Some (fst x), spill_irc (fst x) g (lowest_cost_in _ _ _  H) = snd x -> P
| None => Z = None -> P
end -> P
  
     with
       | Some x => _
       | None => _
     end _).

simpl. intros. apply X with (H0 := H). reflexivity.
auto.
Qed.  

Lemma spill_inv : forall g res,
spill g = Some res ->
lowest_cost (get_spillWL (irc_wl g)) (irc_g g) = Some (fst res).
Proof.
  intros.
  apply spill_inv_aux with g.
  rewrite H.
  auto.
Qed.

Lemma spill_inv2 : forall g res,
spill g = Some res ->
exists H, snd res = spill_irc (fst res) g (lowest_cost_in (fst res) (get_spillWL (irc_wl g)) (irc_g g) H).

Proof.
intros.
apply (spill_inv_aux g). rewrite H.
simpl. intros. rewrite <-H1.
exists H0. reflexivity.
Qed.

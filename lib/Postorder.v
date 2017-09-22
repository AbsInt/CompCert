(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Postorder numbering of a directed graph. *)

Require Import Wellfounded.
Require Import Permutation.
Require Import Mergesort.
Require Import Coqlib.
Require Import Maps.
Require Import Iteration.

(** The graph is presented as a finite map from nodes (of type [positive])
  to the lists of their successors. *)

Definition node: Type := positive.

Definition graph: Type := PTree.t (list node).

(** A sorting function over lists of positives.  While not necessary for
  correctness, we process the successors of a node in increasing order.
  This preserves more of the shape of the original graph and is good for
  our CFG linearization heuristic. *)

Module PositiveOrd.
  Definition t := positive.
  Definition leb (x y: t): bool := if plt y x then false else true.
(*  Infix "<=?" := leb (at level 35). *)
  Theorem leb_total : forall x y, is_true (leb x y) \/ is_true (leb y x).
  Proof.
    unfold leb, is_true; intros.
    destruct (plt x y); auto. destruct (plt y x); auto.
    elim (Plt_strict x). eapply Plt_trans; eauto.
  Qed.
End PositiveOrd.

Module Sort := Mergesort.Sort(PositiveOrd).

(** The traversal is presented as an iteration that modifies the following state. *)

Record state : Type := mkstate {
  gr: graph;                    (**r current graph, without already-visited nodes *)
  wrk: list (node * list node); (**r worklist *)
  map: PTree.t positive;        (**r current mapping node -> postorder number *)
  next: positive                (**r number to use for next numbering *)
}.

Definition init_state (g: graph) (root: node) :=
  match g!root with
  | Some succs =>
     {| gr := PTree.remove root g;
        wrk := (root, Sort.sort succs) :: nil;
        map := PTree.empty positive;
        next := 1%positive |}
  | None =>
     {| gr := g;
        wrk := nil;
        map := PTree.empty positive;
        next := 1%positive |}
  end.

Definition transition (s: state) : PTree.t positive + state :=
  match s.(wrk) with
  | nil =>                              (**r empty worklist, we are done *)
      inl _ s.(map)
  | (x, nil) :: l =>                    (**r all successors of [x] are numbered; number [x] itself *)
      inr _ {| gr := s.(gr);
               wrk := l;
               map := PTree.set x s.(next) s.(map);
               next := Pos.succ s.(next) |}
  | (x, y :: succs_x) :: l =>           (**r consider [y], the next unnumbered successor of [x] *)
      match s.(gr)!y with
      | None =>                         (**r [y] is already numbered: discard from worklist *)
          inr _ {| gr := s.(gr);
                   wrk := (x, succs_x) :: l;
                   map := s.(map);
                   next := s.(next) |}
      | Some succs_y =>                 (**r push [y] on the worklist *)
          inr _ {| gr := PTree.remove y s.(gr);
                   wrk := (y, Sort.sort succs_y) :: (x, succs_x) :: l;
                   map := s.(map);
                   next := s.(next) |}
      end
  end.

Section POSTORDER.

Variable ginit: graph.
Variable root: node.

Inductive invariant (s: state) : Prop :=
  Invariant
    (* current graph is a subset of ginit *)
    (SUB: forall x y, s.(gr)!x = Some y -> ginit!x = Some y)
    (* root is not in current graph *)
    (ROOT: s.(gr)!root = None)
    (* mapped nodes have their numbers below next *)
    (BELOW: forall x y, s.(map)!x = Some y -> Plt y s.(next))
    (* mapping is injective *)
    (INJ: forall x1 x2 y, s.(map)!x1 = Some y -> s.(map)!x2 = Some y -> x1 = x2)
    (* nodes not yet visited have no number *)
    (REM: forall x y, s.(gr)!x = Some y -> s.(map)!x = None)
    (* black nodes have no white son *)
    (COLOR: forall x succs n y,
            ginit!x = Some succs -> s.(map)!x = Some n ->
            In y succs -> s.(gr)!y = None)
    (* worklist is well-formed *)
    (WKLIST: forall x l, In (x, l) s.(wrk) ->
             s.(gr)!x = None /\
             exists l', ginit!x = Some l'
                    /\ forall y, In y l' -> ~In y l -> s.(gr)!y = None)
    (* all grey nodes are on the worklist *)
    (GREY: forall x, ginit!x <> None -> s.(gr)!x = None -> s.(map)!x = None ->
           exists l, In (x,l) s.(wrk)).

Inductive postcondition (map: PTree.t positive) : Prop :=
  Postcondition
    (INJ: forall x1 x2 y, map!x1 = Some y -> map!x2 = Some y -> x1 = x2)
    (ROOT: ginit!root <> None -> map!root <> None)
    (SUCCS: forall x succs y, ginit!x = Some succs -> map!x <> None -> In y succs -> ginit!y <> None -> map!y <> None).

Remark In_sort:
  forall x l, In x l <-> In x (Sort.sort l).
Proof.
  intros; split; intros.
  apply Permutation_in with l. apply Sort.Permuted_sort. auto.
  apply Permutation_in with (Sort.sort l). apply Permutation_sym. apply Sort.Permuted_sort. auto.
Qed.

Lemma transition_spec:
  forall s, invariant s ->
  match transition s with inr s' => invariant s' | inl m => postcondition m end.
Proof.
  intros. inv H. unfold transition. destruct (wrk s) as [ | [x succ_x] l].
  (* finished *)
  constructor; intros.
  eauto.
  caseEq (s.(map)!root); intros. congruence. exploit GREY; eauto. intros [? ?]; contradiction.
  destruct (s.(map)!x) eqn:?; try congruence.
  destruct (s.(map)!y) eqn:?; try congruence.
  exploit COLOR; eauto. intros. exploit GREY; eauto. intros [? ?]; contradiction.
  (* not finished *)
  destruct succ_x as [ | y succ_x ].
  (* all children of x were traversed *)
  constructor; simpl; intros.
  (* sub *)
  eauto.
  (* root *)
  eauto.
  (* below *)
  rewrite PTree.gsspec in H. destruct (peq x0 x). inv H.
  apply Plt_succ.
  apply Plt_trans_succ. eauto.
  (* inj *)
  rewrite PTree.gsspec in H. rewrite PTree.gsspec in H0.
  destruct (peq x1 x); destruct (peq x2 x); subst.
  auto.
  inv H. exploit BELOW; eauto. intros. eelim Plt_strict; eauto.
  inv H0. exploit BELOW; eauto. intros. eelim Plt_strict; eauto.
  eauto.
  (* rem *)
  intros. rewrite PTree.gso; eauto. red; intros; subst x0.
  exploit (WKLIST x nil); auto with coqlib. intros [A B]. congruence.
  (* color *)
  rewrite PTree.gsspec in H0. destruct (peq x0 x).
  inv H0.  exploit (WKLIST x nil); auto with coqlib.
  intros [A [l' [B C]]].
  assert (l' = succs) by congruence. subst l'.
  apply C; auto.
  eauto.
  (* wklist *)
  apply WKLIST. auto with coqlib.
  (* grey *)
  rewrite PTree.gsspec in H1. destruct (peq x0 x). inv H1.
  exploit GREY; eauto. intros [l' A]. simpl in A; destruct A.
  congruence.
  exists l'; auto.

  (* children y needs traversing *)
  destruct ((gr s)!y) as [ succs_y | ] eqn:?.
  (* y has children *)
  constructor; simpl; intros.
  (* sub *)
  rewrite PTree.grspec in H. destruct (PTree.elt_eq x0 y); eauto. inv H.
  (* root *)
  rewrite PTree.gro. auto. congruence.
  (* below *)
  eauto.
  (* inj *)
  eauto.
  (* rem *)
  rewrite PTree.grspec in H. destruct (PTree.elt_eq x0 y); eauto. inv H.
  (* color *)
  rewrite PTree.grspec. destruct (PTree.elt_eq y0 y); eauto.
  (* wklist *)
  destruct H.
  inv H. split. apply PTree.grs. exists succs_y; split. eauto.
  intros. rewrite In_sort in H. tauto.
  destruct H.
  inv H. exploit WKLIST; eauto with coqlib. intros [A [l' [B C]]].
  split. rewrite PTree.grspec. destruct (PTree.elt_eq x0 y); auto.
  exists l'; split. auto. intros. rewrite PTree.grspec. destruct (PTree.elt_eq y0 y); auto.
  apply C; auto. simpl. intuition congruence.
  exploit (WKLIST x0 l0); eauto with coqlib. intros [A [l' [B C]]].
  split. rewrite PTree.grspec. destruct (PTree.elt_eq x0 y); auto.
  exists l'; split; auto. intros.
  rewrite PTree.grspec. destruct (PTree.elt_eq y0 y); auto.
  (* grey *)
  rewrite PTree.grspec in H0. destruct (PTree.elt_eq x0 y) in H0.
  subst. exists (Sort.sort succs_y); auto with coqlib.
  exploit GREY; eauto. simpl. intros [l1 A]. destruct A.
  inv H2. exists succ_x; auto.
  exists l1; auto.

  (* y has no children *)
  constructor; simpl; intros; eauto.
  (* wklist *)
  destruct H. inv H.
  exploit (WKLIST x0); eauto with coqlib. intros [A [l' [B C]]].
  split. auto. exists l'; split. auto.
  intros. destruct (peq y y0). congruence. apply C; auto. simpl. intuition congruence.
  eapply WKLIST; eauto with coqlib.
  (* grey *)
  exploit GREY; eauto. intros [l1 A]. simpl in A. destruct A.
  inv H2. exists succ_x; auto.
  exists l1; auto.
Qed.

Lemma initial_state_spec:
  invariant (init_state ginit root).
Proof.
  unfold init_state. destruct (ginit!root) as [succs|] eqn:?.
  (* root has succs *)
  constructor; simpl; intros.
  (* sub *)
  rewrite PTree.grspec in H. destruct (PTree.elt_eq x root). inv H. auto.
  (* root *)
  apply PTree.grs.
  (* below *)
  rewrite PTree.gempty in H; inv H.
  (* inj *)
  rewrite PTree.gempty in H; inv H.
  (* rem *)
  apply PTree.gempty.
  (* color *)
  rewrite PTree.gempty in H0; inv H0.
  (* wklist *)
  destruct H; inv H.
  split. apply PTree.grs. exists succs; split; auto.
  intros. rewrite In_sort in H. intuition.
  (* grey *)
  rewrite PTree.grspec in H0. destruct (PTree.elt_eq x root).
  subst. exists (Sort.sort succs); auto.
  contradiction.

  (* root has no succs *)
  constructor; simpl; intros.
  (* sub *)
  auto.
  (* root *)
  auto.
  (* below *)
  rewrite PTree.gempty in H; inv H.
  (* inj *)
  rewrite PTree.gempty in H; inv H.
  (* rem *)
  apply PTree.gempty.
  (* color *)
  rewrite PTree.gempty in H0; inv H0.
  (* wklist *)
  contradiction.
  (* grey *)
  contradiction.

Qed.

(** Termination criterion. *)

Fixpoint size_worklist (w: list (positive * list positive)) : nat :=
  match w with
  | nil => 0%nat
  | (x, succs) :: w' => (S (List.length succs) + size_worklist w')%nat
  end.

Definition lt_state (s1 s2: state) : Prop :=
  lex_ord lt lt (PTree_Properties.cardinal s1.(gr), size_worklist s1.(wrk))
                (PTree_Properties.cardinal s2.(gr), size_worklist s2.(wrk)).

Lemma lt_state_wf: well_founded lt_state.
Proof.
  set (f := fun s => (PTree_Properties.cardinal s.(gr), size_worklist s.(wrk))).
  change (well_founded (fun s1 s2 => lex_ord lt lt (f s1) (f s2))).
  apply wf_inverse_image.
  apply wf_lex_ord.
  apply lt_wf. apply lt_wf.
Qed.

Lemma transition_decreases:
  forall s s', transition s = inr _ s' -> lt_state s' s.
Proof.
  unfold transition, lt_state; intros.
  destruct (wrk s) as [ | [x succs] l].
  discriminate.
  destruct succs as [ | y succs ].
  inv H. simpl. apply lex_ord_right. omega.
  destruct ((gr s)!y) as [succs'|] eqn:?.
  inv H. simpl. apply lex_ord_left. eapply PTree_Properties.cardinal_remove; eauto.
  inv H. simpl. apply lex_ord_right. omega.
Qed.

End POSTORDER.

Definition postorder (g: graph) (root: node) :=
  WfIter.iterate _ _ transition lt_state lt_state_wf transition_decreases (init_state g root).

Inductive reachable (g: graph) (root: positive) : positive -> Prop :=
  | reachable_root:
      reachable g root root
  | reachable_succ: forall x succs y,
      reachable g root x -> g!x = Some succs -> In y succs ->
      reachable g root y.

Theorem postorder_correct:
  forall g root,
  let m := postorder g root in
  (forall x1 x2 y, m!x1 = Some y -> m!x2 = Some y -> x1 = x2)
  /\ (forall x, reachable g root x -> g!x <> None -> m!x <> None).
Proof.
  intros.
  assert (postcondition g root m).
    unfold m. unfold postorder.
    apply WfIter.iterate_prop with (P := invariant g root).
    apply transition_spec.
    apply initial_state_spec.
  inv H.
  split. auto.
  induction 1; intros.
  (* root case *)
  apply ROOT; auto.
  (* succ case *)
  eapply SUCCS; eauto. apply IHreachable. congruence.
Qed.


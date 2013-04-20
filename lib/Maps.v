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

(** Applicative finite maps are the main data structure used in this
  project.  A finite map associates data to keys.  The two main operations
  are [set k d m], which returns a map identical to [m] except that [d]
  is associated to [k], and [get k m] which returns the data associated
  to key [k] in map [m].  In this library, we distinguish two kinds of maps:
- Trees: the [get] operation returns an option type, either [None]
  if no data is associated to the key, or [Some d] otherwise.
- Maps: the [get] operation always returns a data.  If no data was explicitly
  associated with the key, a default data provided at map initialization time
  is returned.

  In this library, we provide efficient implementations of trees and
  maps whose keys range over the type [positive] of binary positive
  integers or any type that can be injected into [positive].  The
  implementation is based on radix-2 search trees (uncompressed
  Patricia trees) and guarantees logarithmic-time operations.  An
  inefficient implementation of maps as functions is also provided.
*)

Require Import Equivalence EquivDec.
Require Import Coqlib.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Set Implicit Arguments.

(** * The abstract signatures of trees *)

Module Type TREE.
  Variable elt: Type.
  Variable elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Variable t: Type -> Type.
  Variable empty: forall (A: Type), t A.
  Variable get: forall (A: Type), elt -> t A -> option A.
  Variable set: forall (A: Type), elt -> A -> t A -> t A.
  Variable remove: forall (A: Type), elt -> t A -> t A.

  (** The ``good variables'' properties for trees, expressing
    commutations between [get], [set] and [remove]. *)
  Hypothesis gempty:
    forall (A: Type) (i: elt), get i (empty A) = None.
  Hypothesis gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Hypothesis gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Hypothesis gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Hypothesis gsident:
    forall (A: Type) (i: elt) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.
  (* We could implement the following, but it's not needed for the moment.
    Hypothesis grident:
      forall (A: Type) (i: elt) (m: t A) (v: A),
      get i m = None -> remove i m = m.
  *)
  Hypothesis grs:
    forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Hypothesis gro:
    forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Hypothesis grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.

  (** Extensional equality between trees. *)
  Variable beq: forall (A: Type), (A -> A -> bool) -> t A -> t A -> bool.
  Hypothesis beq_correct:
    forall (A: Type) (eqA: A -> A -> bool) (t1 t2: t A),
    beq eqA t1 t2 = true <->
    (forall (x: elt),
     match get x t1, get x t2 with
     | None, None => True
     | Some y1, Some y2 => eqA y1 y2 = true
     | _, _ => False
    end).

  (** Applying a function to all data of a tree. *)
  Variable map:
    forall (A B: Type), (elt -> A -> B) -> t A -> t B.
  Hypothesis gmap:
    forall (A B: Type) (f: elt -> A -> B) (i: elt) (m: t A),
    get i (map f m) = option_map (f i) (get i m).

  (** Same as [map], but the function does not receive the [elt] argument. *)
  Variable map1:
    forall (A B: Type), (A -> B) -> t A -> t B.
  Hypothesis gmap1:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map1 f m) = option_map f (get i m).

  (** Applying a function pairwise to all data of two trees. *)
  Variable combine:
    forall (A B C: Type), (option A -> option B -> option C) -> t A -> t B -> t C.
  Hypothesis gcombine:
    forall (A B C: Type) (f: option A -> option B -> option C),
    f None None = None ->
    forall (m1: t A) (m2: t B) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).
  Hypothesis combine_commut:
    forall (A B: Type) (f g: option A -> option A -> option B),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.

  (** Enumerating the bindings of a tree. *)
  Variable elements:
    forall (A: Type), t A -> list (elt * A).
  Hypothesis elements_correct:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Hypothesis elements_complete:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Hypothesis elements_keys_norepet:
    forall (A: Type) (m: t A), 
    list_norepet (List.map (@fst elt A) (elements m)).

  (** Folding a function over all bindings of a tree. *)
  Variable fold:
    forall (A B: Type), (B -> elt -> A -> B) -> t A -> B -> B.
  Hypothesis fold_spec:
    forall (A B: Type) (f: B -> elt -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
End TREE.

(** * The abstract signatures of maps *)

Module Type MAP.
  Variable elt: Type.
  Variable elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Variable t: Type -> Type.
  Variable init: forall (A: Type), A -> t A.
  Variable get: forall (A: Type), elt -> t A -> A.
  Variable set: forall (A: Type), elt -> A -> t A -> t A.
  Hypothesis gi:
    forall (A: Type) (i: elt) (x: A), get i (init x) = x.
  Hypothesis gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = x.
  Hypothesis gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Hypothesis gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Hypothesis gsident:
    forall (A: Type) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.
  Variable map: forall (A B: Type), (A -> B) -> t A -> t B.
  Hypothesis gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
End MAP.

(** * An implementation of trees over type [positive] *)

Module PTree <: TREE.
  Definition elt := positive.
  Definition elt_eq := peq.

  Inductive tree (A : Type) : Type :=
    | Leaf : tree A
    | Node : tree A -> option A -> tree A -> tree A.

  Implicit Arguments Leaf [A].
  Implicit Arguments Node [A].
  Scheme tree_ind := Induction for tree Sort Prop.

  Definition t := tree.

  Definition empty (A : Type) := (Leaf : t A).

  Fixpoint get (A : Type) (i : positive) (m : t A) {struct i} : option A :=
    match m with
    | Leaf => None
    | Node l o r =>
        match i with
        | xH => o
        | xO ii => get ii l
        | xI ii => get ii r
        end
    end.

  Fixpoint set (A : Type) (i : positive) (v : A) (m : t A) {struct i} : t A :=
    match m with
    | Leaf =>
        match i with
        | xH => Node Leaf (Some v) Leaf
        | xO ii => Node (set ii v Leaf) None Leaf
        | xI ii => Node Leaf None (set ii v Leaf)
        end
    | Node l o r =>
        match i with
        | xH => Node l (Some v) r
        | xO ii => Node (set ii v l) o r
        | xI ii => Node l o (set ii v r)
        end
    end.

  Fixpoint remove (A : Type) (i : positive) (m : t A) {struct i} : t A :=
    match i with
    | xH =>
        match m with
        | Leaf => Leaf
        | Node Leaf o Leaf => Leaf
        | Node l o r => Node l None r
        end
    | xO ii =>
        match m with
        | Leaf => Leaf
        | Node l None Leaf =>
            match remove ii l with
            | Leaf => Leaf
            | mm => Node mm None Leaf
            end
        | Node l o r => Node (remove ii l) o r
        end
    | xI ii =>
        match m with
        | Leaf => Leaf
        | Node Leaf None r =>
            match remove ii r with
            | Leaf => Leaf
            | mm => Node Leaf None mm
            end
        | Node l o r => Node l o (remove ii r)
        end
    end.

  Theorem gempty:
    forall (A: Type) (i: positive), get i (empty A) = None.
  Proof.
    induction i; simpl; auto.
  Qed.

  Theorem gss:
    forall (A: Type) (i: positive) (x: A) (m: t A), get i (set i x m) = Some x.
  Proof.
    induction i; destruct m; simpl; auto.
  Qed.

    Lemma gleaf : forall (A : Type) (i : positive), get i (Leaf : t A) = None.
    Proof. exact gempty. Qed.

  Theorem gso:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    induction i; intros; destruct j; destruct m; simpl;
       try rewrite <- (gleaf A i); auto; try apply IHi; congruence.
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    get i (set j x m) = if peq i j then Some x else get i m.
  Proof.
    intros.
    destruct (peq i j); [ rewrite e; apply gss | apply gso; auto ].
  Qed.

  Theorem gsident:
    forall (A: Type) (i: positive) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.
  Proof.
    induction i; intros; destruct m; simpl; simpl in H; try congruence.
     rewrite (IHi m2 v H); congruence.
     rewrite (IHi m1 v H); congruence.
  Qed.

  Theorem set2:
    forall (A: Type) (i: elt) (m: t A) (v1 v2: A),
    set i v2 (set i v1 m) = set i v2 m.
  Proof.
    induction i; intros; destruct m; simpl; try (rewrite IHi); auto.
  Qed.

  Lemma rleaf : forall (A : Type) (i : positive), remove i (Leaf : t A) = Leaf.
  Proof. destruct i; simpl; auto. Qed.

  Theorem grs:
    forall (A: Type) (i: positive) (m: t A), get i (remove i m) = None.
  Proof.
    induction i; destruct m.
     simpl; auto.
     destruct m1; destruct o; destruct m2 as [ | ll oo rr]; simpl; auto.
      rewrite (rleaf A i); auto.
      cut (get i (remove i (Node ll oo rr)) = None).
        destruct (remove i (Node ll oo rr)); auto; apply IHi.
        apply IHi.
     simpl; auto.
     destruct m1 as [ | ll oo rr]; destruct o; destruct m2; simpl; auto.
      rewrite (rleaf A i); auto.
      cut (get i (remove i (Node ll oo rr)) = None).
        destruct (remove i (Node ll oo rr)); auto; apply IHi.
        apply IHi.
     simpl; auto.
     destruct m1; destruct m2; simpl; auto.
  Qed.

  Theorem gro:
    forall (A: Type) (i j: positive) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Proof.
    induction i; intros; destruct j; destruct m;
        try rewrite (rleaf A (xI j));
        try rewrite (rleaf A (xO j));
        try rewrite (rleaf A 1); auto;
        destruct m1; destruct o; destruct m2;
        simpl;
        try apply IHi; try congruence;
        try rewrite (rleaf A j); auto;
        try rewrite (gleaf A i); auto.
     cut (get i (remove j (Node m2_1 o m2_2)) = get i (Node m2_1 o m2_2));
        [ destruct (remove j (Node m2_1 o m2_2)); try rewrite (gleaf A i); auto
        | apply IHi; congruence ].
     destruct (remove j (Node m1_1 o0 m1_2)); simpl; try rewrite (gleaf A i);
        auto.
     destruct (remove j (Node m2_1 o m2_2)); simpl; try rewrite (gleaf A i);
        auto.
     cut (get i (remove j (Node m1_1 o0 m1_2)) = get i (Node m1_1 o0 m1_2));
        [ destruct (remove j (Node m1_1 o0 m1_2)); try rewrite (gleaf A i); auto
        | apply IHi; congruence ].
     destruct (remove j (Node m2_1 o m2_2)); simpl; try rewrite (gleaf A i);
        auto.
     destruct (remove j (Node m1_1 o0 m1_2)); simpl; try rewrite (gleaf A i);
        auto.
  Qed.

  Theorem grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof.
    intros. destruct (elt_eq i j). subst j. apply grs. apply gro; auto.
  Qed.

  Section BOOLEAN_EQUALITY.

    Variable A: Type.
    Variable beqA: A -> A -> bool.

    Fixpoint bempty (m: t A) : bool :=
      match m with
      | Leaf => true
      | Node l None r => bempty l && bempty r
      | Node l (Some _) r => false
      end.

    Fixpoint beq (m1 m2: t A) {struct m1} : bool :=
      match m1, m2 with
      | Leaf, _ => bempty m2
      | _, Leaf => bempty m1
      | Node l1 o1 r1, Node l2 o2 r2 =>
          match o1, o2 with
          | None, None => true
          | Some y1, Some y2 => beqA y1 y2
          | _, _ => false
          end
          && beq l1 l2 && beq r1 r2
      end.

    Lemma bempty_correct:
      forall m, bempty m = true <-> (forall x, get x m = None).
    Proof.
      induction m; simpl.
      split; intros. apply gleaf. auto.
      destruct o; split; intros.
      congruence.
      generalize (H xH); simpl; congruence.
      destruct (andb_prop _ _ H). rewrite IHm1 in H0. rewrite IHm2 in H1.
      destruct x; simpl; auto.
      apply andb_true_intro; split. 
      apply IHm1. intros; apply (H (xO x)).
      apply IHm2. intros; apply (H (xI x)).
    Qed.

    Lemma beq_correct:
      forall m1 m2,
      beq m1 m2 = true <->
      (forall (x: elt),
       match get x m1, get x m2 with
       | None, None => True
       | Some y1, Some y2 => beqA y1 y2 = true
       | _, _ => False
       end).
    Proof.
      induction m1; intros.
    - simpl. rewrite bempty_correct. split; intros.
      rewrite gleaf. rewrite H. auto.
      generalize (H x). rewrite gleaf. destruct (get x m2); tauto. 
    - destruct m2.
      + unfold beq. rewrite bempty_correct. split; intros.
        rewrite H. rewrite gleaf. auto.
        generalize (H x). rewrite gleaf. destruct (get x (Node m1_1 o m1_2)); tauto.
      + simpl. split; intros.
        * destruct (andb_prop _ _ H). destruct (andb_prop _ _ H0).
          rewrite IHm1_1 in H3. rewrite IHm1_2 in H1. 
          destruct x; simpl. apply H1. apply H3.
          destruct o; destruct o0; auto || congruence.
        * apply andb_true_intro. split. apply andb_true_intro. split.
          generalize (H xH); simpl. destruct o; destruct o0; tauto. 
          apply IHm1_1. intros; apply (H (xO x)).
          apply IHm1_2. intros; apply (H (xI x)).
    Qed.

  End BOOLEAN_EQUALITY.

    Fixpoint append (i j : positive) {struct i} : positive :=
      match i with
      | xH => j
      | xI ii => xI (append ii j)
      | xO ii => xO (append ii j)
      end.

    Lemma append_assoc_0 : forall (i j : positive),
                           append i (xO j) = append (append i (xO xH)) j.
    Proof.
      induction i; intros; destruct j; simpl;
      try rewrite (IHi (xI j));
      try rewrite (IHi (xO j));
      try rewrite <- (IHi xH);
      auto.
    Qed.

    Lemma append_assoc_1 : forall (i j : positive),
                           append i (xI j) = append (append i (xI xH)) j.
    Proof.
      induction i; intros; destruct j; simpl;
      try rewrite (IHi (xI j));
      try rewrite (IHi (xO j));
      try rewrite <- (IHi xH);
      auto.
    Qed.

    Lemma append_neutral_r : forall (i : positive), append i xH = i.
    Proof.
      induction i; simpl; congruence.
    Qed.

    Lemma append_neutral_l : forall (i : positive), append xH i = i.
    Proof.
      simpl; auto.
    Qed.

    Fixpoint xmap (A B : Type) (f : positive -> A -> B) (m : t A) (i : positive)
             {struct m} : t B :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node (xmap f l (append i (xO xH)))
                           (option_map (f i) o)
                           (xmap f r (append i (xI xH)))
      end.

  Definition map (A B : Type) (f : positive -> A -> B) m := xmap f m xH.

    Lemma xgmap:
      forall (A B: Type) (f: positive -> A -> B) (i j : positive) (m: t A),
      get i (xmap f m j) = option_map (f (append j i)) (get i m).
    Proof.
      induction i; intros; destruct m; simpl; auto.
      rewrite (append_assoc_1 j i); apply IHi.
      rewrite (append_assoc_0 j i); apply IHi.
      rewrite (append_neutral_r j); auto.
    Qed.

  Theorem gmap:
    forall (A B: Type) (f: positive -> A -> B) (i: positive) (m: t A),
    get i (map f m) = option_map (f i) (get i m).
  Proof.
    intros.
    unfold map.
    replace (f i) with (f (append xH i)).
    apply xgmap.
    rewrite append_neutral_l; auto.
  Qed.

  Fixpoint map1 (A B: Type) (f: A -> B) (m: t A) {struct m} : t B :=
    match m with
    | Leaf => Leaf
    | Node l o r => Node (map1 f l) (option_map f o) (map1 f r)
    end.

  Theorem gmap1:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map1 f m) = option_map f (get i m).
  Proof.
    induction i; intros; destruct m; simpl; auto.
  Qed.

  Definition Node' (A: Type) (l: t A) (x: option A) (r: t A): t A :=
    match l, x, r with
    | Leaf, None, Leaf => Leaf
    | _, _, _ => Node l x r
    end.

  Lemma gnode':
    forall (A: Type) (l r: t A) (x: option A) (i: positive),
    get i (Node' l x r) = get i (Node l x r).
  Proof.
    intros. unfold Node'. 
    destruct l; destruct x; destruct r; auto.
    destruct i; simpl; auto; rewrite gleaf; auto.
  Qed.

  Fixpoint filter1 (A: Type) (pred: A -> bool) (m: t A) {struct m} : t A :=
    match m with
    | Leaf => Leaf
    | Node l o r =>
        let o' := match o with None => None | Some x => if pred x then o else None end in
        Node' (filter1 pred l) o' (filter1 pred r)
    end.

  Theorem gfilter1:
    forall (A: Type) (pred: A -> bool) (i: elt) (m: t A),
    get i (filter1 pred m) =
    match get i m with None => None | Some x => if pred x then Some x else None end.
  Proof.
    intros until m. revert m i. induction m; simpl; intros. 
    rewrite gleaf; auto.
    rewrite gnode'. destruct i; simpl; auto. destruct o; auto. 
  Qed.

  Section COMBINE.

  Variables A B C: Type.
  Variable f: option A -> option B -> option C.
  Hypothesis f_none_none: f None None = None.

  Fixpoint xcombine_l (m : t A) {struct m} : t C :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node' (xcombine_l l) (f o None) (xcombine_l r)
      end.

  Lemma xgcombine_l :
          forall (m: t A) (i : positive),
          get i (xcombine_l m) = f (get i m) None.
    Proof.
      induction m; intros; simpl.
      repeat rewrite gleaf. auto.
      rewrite gnode'. destruct i; simpl; auto.
    Qed.

  Fixpoint xcombine_r (m : t B) {struct m} : t C :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node' (xcombine_r l) (f None o) (xcombine_r r)
      end.

  Lemma xgcombine_r :
          forall (m: t B) (i : positive),
          get i (xcombine_r m) = f None (get i m).
    Proof.
      induction m; intros; simpl.
      repeat rewrite gleaf. auto.
      rewrite gnode'. destruct i; simpl; auto.
    Qed.

  Fixpoint combine (m1: t A) (m2: t B) {struct m1} : t C :=
    match m1 with
    | Leaf => xcombine_r m2
    | Node l1 o1 r1 =>
        match m2 with
        | Leaf => xcombine_l m1
        | Node l2 o2 r2 => Node' (combine l1 l2) (f o1 o2) (combine r1 r2)
        end
    end.

  Theorem gcombine:
      forall (m1: t A) (m2: t B) (i: positive),
      get i (combine m1 m2) = f (get i m1) (get i m2).
  Proof.
    induction m1; intros; simpl.
    rewrite gleaf. apply xgcombine_r.
    destruct m2; simpl.
    rewrite gleaf. rewrite <- xgcombine_l. auto. 
    repeat rewrite gnode'. destruct i; simpl; auto.
  Qed.

  End COMBINE.

  Lemma xcombine_lr :
    forall (A B: Type) (f g : option A -> option A -> option B) (m : t A),
    (forall (i j : option A), f i j = g j i) ->
    xcombine_l f m = xcombine_r g m.
    Proof.
      induction m; intros; simpl; auto.
      rewrite IHm1; auto.
      rewrite IHm2; auto.
      rewrite H; auto.
    Qed.

  Theorem combine_commut:
    forall (A B: Type) (f g: option A -> option A -> option B),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.
  Proof.
    intros A B f g EQ1.
    assert (EQ2: forall (i j: option A), g i j = f j i).
      intros; auto.
    induction m1; intros; destruct m2; simpl;
      try rewrite EQ1;
      repeat rewrite (xcombine_lr f g);
      repeat rewrite (xcombine_lr g f);
      auto.
     rewrite IHm1_1.
     rewrite IHm1_2.
     auto. 
  Qed.

    Fixpoint xelements (A : Type) (m : t A) (i : positive) 
                       (k: list (positive * A)) {struct m}
                       : list (positive * A) :=
      match m with
      | Leaf => k
      | Node l None r =>
          xelements l (append i (xO xH)) (xelements r (append i (xI xH)) k)
      | Node l (Some x) r =>
          xelements l (append i (xO xH))
            ((i, x) :: xelements r (append i (xI xH)) k)
      end.


  Definition elements (A: Type) (m : t A) := xelements m xH nil.

    Lemma xelements_incl:
      forall (A: Type) (m: t A) (i : positive) k x,
      In x k -> In x (xelements m i k).
    Proof.
      induction m; intros; simpl.
      auto.
      destruct o.
      apply IHm1. simpl; right; auto.
      auto.
    Qed.

    Lemma xelements_correct:
      forall (A: Type) (m: t A) (i j : positive) (v: A) k,
      get i m = Some v -> In (append j i, v) (xelements m j k).
    Proof.
      induction m; intros.
       rewrite (gleaf A i) in H; congruence.
       destruct o; destruct i; simpl; simpl in H.
        rewrite append_assoc_1. apply xelements_incl. right. auto.
        rewrite append_assoc_0. auto. 
        inv H. apply xelements_incl. left. rewrite append_neutral_r; auto.
        rewrite append_assoc_1. apply xelements_incl. auto. 
        rewrite append_assoc_0. auto. 
        inv H.
    Qed.

  Theorem elements_correct:
    forall (A: Type) (m: t A) (i: positive) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Proof.
    intros A m i v H. 
    exact (xelements_correct m i xH nil H).
  Qed.

    Fixpoint xget (A : Type) (i j : positive) (m : t A) {struct j} : option A :=
      match i, j with
      | _, xH => get i m
      | xO ii, xO jj => xget ii jj m
      | xI ii, xI jj => xget ii jj m
      | _, _ => None
      end.

    Lemma xget_diag :
      forall (A : Type) (i : positive) (m1 m2 : t A) (o : option A),
      xget i i (Node m1 o m2) = o.
    Proof.
      induction i; intros; simpl; auto.
    Qed.

    Lemma xget_left :
      forall (A : Type) (j i : positive) (m1 m2 : t A) (o : option A) (v : A),
      xget i (append j (xO xH)) m1 = Some v -> xget i j (Node m1 o m2) = Some v.
    Proof.
      induction j; intros; destruct i; simpl; simpl in H; auto; try congruence.
      destruct i; congruence.
    Qed.

    Lemma xget_right :
      forall (A : Type) (j i : positive) (m1 m2 : t A) (o : option A) (v : A),
      xget i (append j (xI xH)) m2 = Some v -> xget i j (Node m1 o m2) = Some v.
    Proof.
      induction j; intros; destruct i; simpl; simpl in H; auto; try congruence.
      destruct i; congruence.
    Qed.

    Lemma xelements_complete:
      forall (A: Type) (m: t A) (i j : positive) (v: A) k,
      In (i, v) (xelements m j k) -> xget i j m = Some v \/ In (i, v) k.
    Proof.
      induction m; simpl; intros.
      auto.
      destruct o. 
      edestruct IHm1; eauto. left; apply xget_left; auto.
      destruct H0. inv H0. left; apply xget_diag. 
      edestruct IHm2; eauto. left; apply xget_right; auto.
      edestruct IHm1; eauto. left; apply xget_left; auto.
      edestruct IHm2; eauto. left; apply xget_right; auto.
    Qed.

    Lemma get_xget_h :
      forall (A: Type) (m: t A) (i: positive), get i m = xget i xH m.
    Proof.
      destruct i; simpl; auto.
    Qed.

  Theorem elements_complete:
    forall (A: Type) (m: t A) (i: positive) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Proof.
    intros A m i v H. unfold elements in H.
    edestruct xelements_complete; eauto. 
    rewrite get_xget_h. auto. 
    contradiction.
  Qed.

  Lemma in_xelements:
    forall (A: Type) (m: t A) (i k: positive) (v: A) l,
    In (k, v) (xelements m i l) ->
    (exists j, k = append i j) \/ In (k, v) l.
  Proof.
    induction m; simpl; intros.
    auto.
    destruct o.
    edestruct IHm1 as [[j EQ] | IN]; eauto.
    rewrite <- append_assoc_0 in EQ. left; econstructor; eauto. 
    destruct IN.
    inv H0. left; exists xH; symmetry; apply append_neutral_r.
    edestruct IHm2 as [[j EQ] | IN]; eauto.
    rewrite <- append_assoc_1 in EQ. left; econstructor; eauto. 
    edestruct IHm1 as [[j EQ] | IN]; eauto.
    rewrite <- append_assoc_0 in EQ. left; econstructor; eauto. 
    edestruct IHm2 as [[j EQ] | IN']; eauto.
    rewrite <- append_assoc_1 in EQ. left; econstructor; eauto.
  Qed.

  Definition xkeys (A: Type) (m: t A) (i: positive) (l: list (positive * A)) :=
    List.map (@fst positive A) (xelements m i l).

  Lemma in_xkeys:
    forall (A: Type) (m: t A) (i k: positive) l,
    In k (xkeys m i l) ->
    (exists j, k = append i j) \/ In k (List.map fst l).
  Proof.
    unfold xkeys; intros.
    exploit list_in_map_inv; eauto. intros [[k1 v1] [EQ IN]].
    simpl in EQ; subst k1.
    exploit in_xelements; eauto. intros [EX | IN'].
    auto.
    right. change k with (fst (k, v1)). apply List.in_map; auto.
  Qed.

  Lemma append_injective:
    forall i j1 j2, append i j1 = append i j2 -> j1 = j2.
  Proof.
    induction i; simpl; intros.
    apply IHi. congruence.
    apply IHi. congruence.
    auto.
  Qed.

  Lemma xelements_keys_norepet:
    forall (A: Type) (m: t A) (i: positive) l,
    (forall k v, get k m = Some v -> ~In (append i k) (List.map fst l)) ->
    list_norepet (List.map fst l) ->
    list_norepet (xkeys m i l).
  Proof.
    unfold xkeys; induction m; simpl; intros.
    auto.
    destruct o.
    apply IHm1. 
    intros; red; intros IN. rewrite <- append_assoc_0 in IN. simpl in IN; destruct IN.
    exploit (append_injective i k~0 xH). rewrite append_neutral_r. auto.
    congruence.
    exploit in_xkeys; eauto. intros [[j EQ] | IN]. 
    rewrite <- append_assoc_1 in EQ. exploit append_injective; eauto. congruence.
    elim (H (xO k) v); auto.
    simpl. constructor. 
    red; intros IN. exploit in_xkeys; eauto. intros [[j EQ] | IN'].
    rewrite <- append_assoc_1 in EQ. 
    exploit (append_injective i j~1 xH). rewrite append_neutral_r. auto. congruence.
    elim (H xH a). auto. rewrite append_neutral_r. auto.
    apply IHm2; auto. intros. rewrite <- append_assoc_1. eapply H; eauto. 
    apply IHm1. 
    intros; red; intros IN. rewrite <- append_assoc_0 in IN.
    exploit in_xkeys; eauto. intros [[j EQ] | IN']. 
    rewrite <- append_assoc_1 in EQ. exploit append_injective; eauto. congruence.
    elim (H (xO k) v); auto.
    apply IHm2; auto. intros. rewrite <- append_assoc_1. eapply H; eauto. 
  Qed.

  Theorem elements_keys_norepet:
    forall (A: Type) (m: t A), 
    list_norepet (List.map (@fst elt A) (elements m)).
  Proof.
    intros. change (list_norepet (xkeys m 1 nil)). apply xelements_keys_norepet.
    intros; red; intros. elim H0. constructor.
  Qed.

  Remark xelements_empty:
    forall (A: Type) (m: t A) i l, (forall i, get i m = None) -> xelements m i l = l.
  Proof.
    induction m; simpl; intros. 
    auto.
    destruct o. generalize (H xH); simpl; congruence. 
    rewrite IHm1. apply IHm2. 
    intros. apply (H (xI i0)).
    intros. apply (H (xO i0)).
  Qed.

  Theorem elements_canonical_order:
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
    (forall i x, get i m = Some x -> exists y, get i n = Some y /\ R x y) ->
    (forall i y, get i n = Some y -> exists x, get i m = Some x /\ R x y) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (elements m) (elements n).
  Proof.
    intros until R.
    assert (forall m n j l1 l2,
    (forall i x, get i m = Some x -> exists y, get i n = Some y /\ R x y) ->
    (forall i y, get i n = Some y -> exists x, get i m = Some x /\ R x y) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      l1 l2 ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (xelements m j l1) (xelements n j l2)).
  {
    induction m; simpl; intros.
    rewrite xelements_empty. auto. 
    intros. destruct (get i n) eqn:E; auto. exploit H0; eauto. 
    intros [x [P Q]]. rewrite gleaf in P; congruence.
    destruct o. 
    destruct n. exploit (H xH a); auto. simpl. intros [y [P Q]]; congruence.
    exploit (H xH a); auto. intros [y [P Q]]. simpl in P. subst o. 
    simpl. apply IHm1. 
    intros i x. exact (H (xO i) x). 
    intros i x. exact (H0 (xO i) x).
    constructor. simpl; auto. 
    apply IHm2. 
    intros i x. exact (H (xI i) x). 
    intros i x. exact (H0 (xI i) x).
    auto.
    destruct n. simpl. 
    rewrite ! xelements_empty. auto.
    intros. destruct (get i m2) eqn:E; auto. exploit (H (xI i)); eauto.
    rewrite gleaf. intros [y [P Q]]; congruence.
    intros. destruct (get i m1) eqn:E; auto. exploit (H (xO i)); eauto.
    rewrite gleaf. intros [y [P Q]]; congruence.
    destruct o. 
    exploit (H0 xH); simpl; eauto. intros [y [P Q]]; congruence.
    simpl. apply IHm1. 
    intros i x. exact (H (xO i) x). 
    intros i x. exact (H0 (xO i) x).
    apply IHm2. 
    intros i x. exact (H (xI i) x). 
    intros i x. exact (H0 (xI i) x).
    auto.
  }
    intros. apply H. auto. auto. constructor.
  Qed.

  Theorem elements_extensional:
    forall (A: Type) (m n: t A),
    (forall i, get i m = get i n) ->
    elements m = elements n.
  Proof.
    intros. 
    exploit (elements_canonical_order (fun (x y: A) => x = y) m n). 
    intros. rewrite H in H0. exists x; auto.
    intros. rewrite <- H in H0. exists y; auto.
    induction 1. auto. destruct a1 as [a2 a3]; destruct b1 as [b2 b3]; simpl in *.
    destruct H0. congruence.
  Qed.

  Fixpoint xfold (A B: Type) (f: B -> positive -> A -> B)
                 (i: positive) (m: t A) (v: B) {struct m} : B :=
    match m with
    | Leaf => v
    | Node l None r =>
        let v1 := xfold f (append i (xO xH)) l v in
        xfold f (append i (xI xH)) r v1
    | Node l (Some x) r =>
        let v1 := xfold f (append i (xO xH)) l v in
        let v2 := f v1 i x in
        xfold f (append i (xI xH)) r v2
    end.

  Definition fold (A B : Type) (f: B -> positive -> A -> B) (m: t A) (v: B) :=
    xfold f xH m v.

  Lemma xfold_xelements:
    forall (A B: Type) (f: B -> positive -> A -> B) m i v l,
    List.fold_left (fun a p => f a (fst p) (snd p)) l (xfold f i m v) =
    List.fold_left (fun a p => f a (fst p) (snd p)) (xelements m i l) v.
  Proof.
    induction m; intros.
    simpl. auto.
    destruct o; simpl.
    rewrite <- IHm1. simpl. rewrite <- IHm2. auto.
    rewrite <- IHm1. rewrite <- IHm2. auto. 
  Qed.

  Theorem fold_spec:
    forall (A B: Type) (f: B -> positive -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  Proof.
    intros. unfold fold, elements. rewrite <- xfold_xelements. auto. 
  Qed.

End PTree.

(** * An implementation of maps over type [positive] *)

Module PMap <: MAP.
  Definition elt := positive.
  Definition elt_eq := peq.

  Definition t (A : Type) : Type := (A * PTree.t A)%type.

  Definition init (A : Type) (x : A) :=
    (x, PTree.empty A).

  Definition get (A : Type) (i : positive) (m : t A) :=
    match PTree.get i (snd m) with
    | Some x => x
    | None => fst m
    end.

  Definition set (A : Type) (i : positive) (x : A) (m : t A) :=
    (fst m, PTree.set i x (snd m)).

  Theorem gi:
    forall (A: Type) (i: positive) (x: A), get i (init x) = x.
  Proof.
    intros. unfold init. unfold get. simpl. rewrite PTree.gempty. auto.
  Qed.

  Theorem gss:
    forall (A: Type) (i: positive) (x: A) (m: t A), get i (set i x m) = x.
  Proof.
    intros. unfold get. unfold set. simpl. rewrite PTree.gss. auto.
  Qed.

  Theorem gso:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. unfold get. unfold set. simpl. rewrite PTree.gso; auto.
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    get i (set j x m) = if peq i j then x else get i m.
  Proof.
    intros. destruct (peq i j).
     rewrite e. apply gss. auto.
     apply gso. auto.
  Qed.

  Theorem gsident:
    forall (A: Type) (i j: positive) (m: t A),
    get j (set i (get i m) m) = get j m.
  Proof.
    intros. destruct (peq i j).
     rewrite e. rewrite gss. auto.
     rewrite gso; auto.
  Qed.

  Definition map (A B : Type) (f : A -> B) (m : t A) : t B :=
    (f (fst m), PTree.map1 f (snd m)).

  Theorem gmap:
    forall (A B: Type) (f: A -> B) (i: positive) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold map. unfold get. simpl. rewrite PTree.gmap1.
    unfold option_map. destruct (PTree.get i (snd m)); auto.
  Qed.

  Theorem set2:
    forall (A: Type) (i: elt) (x y: A) (m: t A),
    set i y (set i x m) = set i y m.
  Proof.
    intros. unfold set. simpl. decEq. apply PTree.set2.
  Qed.

End PMap.

(** * An implementation of maps over any type that injects into type [positive] *)

Module Type INDEXED_TYPE.
  Variable t: Type.
  Variable index: t -> positive.
  Hypothesis index_inj: forall (x y: t), index x = index y -> x = y.
  Variable eq: forall (x y: t), {x = y} + {x <> y}.
End INDEXED_TYPE.

Module IMap(X: INDEXED_TYPE).

  Definition elt := X.t.
  Definition elt_eq := X.eq.
  Definition t : Type -> Type := PMap.t.
  Definition init (A: Type) (x: A) := PMap.init x.
  Definition get (A: Type) (i: X.t) (m: t A) := PMap.get (X.index i) m.
  Definition set (A: Type) (i: X.t) (v: A) (m: t A) := PMap.set (X.index i) v m.
  Definition map (A B: Type) (f: A -> B) (m: t A) : t B := PMap.map f m.

  Lemma gi:
    forall (A: Type) (x: A) (i: X.t), get i (init x) = x.
  Proof.
    intros. unfold get, init. apply PMap.gi. 
  Qed.

  Lemma gss:
    forall (A: Type) (i: X.t) (x: A) (m: t A), get i (set i x m) = x.
  Proof.
    intros. unfold get, set. apply PMap.gss.
  Qed.

  Lemma gso:
    forall (A: Type) (i j: X.t) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. unfold get, set. apply PMap.gso. 
    red. intro. apply H. apply X.index_inj; auto. 
  Qed.

  Lemma gsspec:
    forall (A: Type) (i j: X.t) (x: A) (m: t A),
    get i (set j x m) = if X.eq i j then x else get i m.
  Proof.
    intros. unfold get, set. 
    rewrite PMap.gsspec.
    case (X.eq i j); intro.
    subst j. rewrite peq_true. reflexivity.
    rewrite peq_false. reflexivity. 
    red; intro. elim n. apply X.index_inj; auto.
  Qed.

  Lemma gmap:
    forall (A B: Type) (f: A -> B) (i: X.t) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold map, get. apply PMap.gmap. 
  Qed.

  Lemma set2:
    forall (A: Type) (i: elt) (x y: A) (m: t A),
    set i y (set i x m) = set i y m.
  Proof.
    intros. unfold set. apply PMap.set2.
  Qed.

End IMap.

Module ZIndexed.
  Definition t := Z.
  Definition index (z: Z): positive :=
    match z with
    | Z0 => xH
    | Zpos p => xO p
    | Zneg p => xI p
    end.
  Lemma index_inj: forall (x y: Z), index x = index y -> x = y.
  Proof.
    unfold index; destruct x; destruct y; intros;
    try discriminate; try reflexivity.
    congruence.
    congruence.
  Qed.
  Definition eq := zeq.
End ZIndexed.

Module ZMap := IMap(ZIndexed).

Module NIndexed.
  Definition t := N.
  Definition index (n: N): positive :=
    match n with
    | N0 => xH
    | Npos p => xO p
    end.
  Lemma index_inj: forall (x y: N), index x = index y -> x = y.
  Proof.
    unfold index; destruct x; destruct y; intros;
    try discriminate; try reflexivity.
    congruence.
  Qed.
  Lemma eq: forall (x y: N), {x = y} + {x <> y}.
  Proof.
    decide equality. apply peq.
  Qed.
End NIndexed.

Module NMap := IMap(NIndexed).

(** * An implementation of maps over any type with decidable equality *)

Module Type EQUALITY_TYPE.
  Variable t: Type.
  Variable eq: forall (x y: t), {x = y} + {x <> y}.
End EQUALITY_TYPE.

Module EMap(X: EQUALITY_TYPE) <: MAP.

  Definition elt := X.t.
  Definition elt_eq := X.eq.
  Definition t (A: Type) := X.t -> A.
  Definition init (A: Type) (v: A) := fun (_: X.t) => v.
  Definition get (A: Type) (x: X.t) (m: t A) := m x.
  Definition set (A: Type) (x: X.t) (v: A) (m: t A) :=
    fun (y: X.t) => if X.eq y x then v else m y.
  Lemma gi:
    forall (A: Type) (i: elt) (x: A), init x i = x.
  Proof.
    intros. reflexivity.
  Qed.
  Lemma gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), (set i x m) i = x.
  Proof.
    intros. unfold set. case (X.eq i i); intro.
    reflexivity. tauto.
  Qed.
  Lemma gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> (set j x m) i = m i.
  Proof.
    intros. unfold set. case (X.eq i j); intro.
    congruence. reflexivity.
  Qed.
  Lemma gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Proof.
    intros. unfold get, set, elt_eq. reflexivity.
  Qed.
  Lemma gsident:
    forall (A: Type) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.
  Proof.
    intros. unfold get, set. case (X.eq j i); intro.
    congruence. reflexivity.
  Qed.
  Definition map (A B: Type) (f: A -> B) (m: t A) :=
    fun (x: X.t) => f(m x).
  Lemma gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold get, map. reflexivity.
  Qed.
End EMap.

(** * Additional properties over trees *)

Module Tree_Properties(T: TREE).

(** An induction principle over [fold]. *)

Section TREE_FOLD_IND.

Variables V A: Type.
Variable f: A -> T.elt -> V -> A.
Variable P: T.t V -> A -> Prop.
Variable init: A.
Variable m_final: T.t V.

Hypothesis P_compat:
  forall m m' a,
  (forall x, T.get x m = T.get x m') ->
  P m a -> P m' a.

Hypothesis H_base: 
  P (T.empty _) init.

Hypothesis H_rec:
  forall m a k v,
  T.get k m = None -> T.get k m_final = Some v -> P m a -> P (T.set k v m) (f a k v).

Let f' (a: A) (p : T.elt * V) := f a (fst p) (snd p).

Let P' (l: list (T.elt * V)) (a: A) : Prop :=
  forall m, list_equiv l (T.elements m) -> P m a.

Remark H_base':
  P' nil init.
Proof.
  red; intros. apply P_compat with (T.empty _); auto.
  intros. rewrite T.gempty. symmetry. case_eq (T.get x m); intros; auto.
  assert (In (x, v) nil). rewrite (H (x, v)). apply T.elements_correct. auto.
  contradiction.
Qed.

Remark H_rec':
  forall k v l a,
  ~In k (List.map (@fst T.elt V) l) ->
  In (k, v) (T.elements m_final) ->
  P' l a ->
  P' (l ++ (k, v) :: nil) (f a k v).
Proof.
  unfold P'; intros.  
  set (m0 := T.remove k m). 
  apply P_compat with (T.set k v m0).
    intros. unfold m0. rewrite T.gsspec. destruct (T.elt_eq x k).
    symmetry. apply T.elements_complete. rewrite <- (H2 (x, v)).
    apply in_or_app. simpl. intuition congruence.
    apply T.gro. auto.
  apply H_rec. unfold m0. apply T.grs. apply T.elements_complete. auto. 
  apply H1. red. intros [k' v']. 
  split; intros. 
  apply T.elements_correct. unfold m0. rewrite T.gro. apply T.elements_complete. 
  rewrite <- (H2 (k', v')). apply in_or_app. auto. 
  red; intro; subst k'. elim H. change k with (fst (k, v')). apply in_map. auto.
  assert (T.get k' m0 = Some v'). apply T.elements_complete. auto.
  unfold m0 in H4. rewrite T.grspec in H4. destruct (T.elt_eq k' k). congruence.
  assert (In (k', v') (T.elements m)). apply T.elements_correct; auto.
  rewrite <- (H2 (k', v')) in H5. destruct (in_app_or _ _ _ H5). auto. 
  simpl in H6. intuition congruence.
Qed.

Lemma fold_rec_aux:
  forall l1 l2 a,
  list_equiv (l2 ++ l1) (T.elements m_final) ->
  list_disjoint (List.map (@fst T.elt V) l1) (List.map (@fst T.elt V) l2) ->
  list_norepet (List.map (@fst T.elt V) l1) ->
  P' l2 a -> P' (l2 ++ l1) (List.fold_left f' l1 a).
Proof.
  induction l1; intros; simpl.
  rewrite <- List.app_nil_end. auto.
  destruct a as [k v]; simpl in *. inv H1. 
  change ((k, v) :: l1) with (((k, v) :: nil) ++ l1). rewrite <- List.app_ass. apply IHl1.
  rewrite app_ass. auto.
  red; intros. rewrite map_app in H3. destruct (in_app_or _ _ _ H3). apply H0; auto with coqlib. 
  simpl in H4. intuition congruence.
  auto.
  unfold f'. simpl. apply H_rec'; auto. eapply list_disjoint_notin; eauto with coqlib.
  rewrite <- (H (k, v)). apply in_or_app. simpl. auto.
Qed.

Theorem fold_rec:
  P m_final (T.fold f m_final init).
Proof.
  intros. rewrite T.fold_spec. fold f'.
  assert (P' (nil ++ T.elements m_final) (List.fold_left f' (T.elements m_final) init)).
    apply fold_rec_aux.
    simpl. red; intros; tauto.
    simpl. red; intros. elim H0.
    apply T.elements_keys_norepet. 
    apply H_base'. 
  simpl in H. red in H. apply H. red; intros. tauto.
Qed.

End TREE_FOLD_IND.

(** A nonnegative measure over trees *)

Section MEASURE.

Variable V: Type.

Definition cardinal (x: T.t V) : nat := List.length (T.elements x).

Remark list_incl_length:
  forall (A: Type) (l1: list A), list_norepet l1 ->
  forall (l2: list A), List.incl l1 l2 -> (List.length l1 <= List.length l2)%nat.
Proof.
  induction 1; simpl; intros.
  omega.
  exploit (List.in_split hd l2). auto with coqlib. intros [l3 [l4 EQ]]. subst l2.
  assert (length tl <= length (l3 ++ l4))%nat.
    apply IHlist_norepet. red; intros. 
    exploit (H1 a); auto with coqlib. 
    repeat rewrite in_app_iff. simpl. intuition. subst. contradiction.
  repeat rewrite app_length in *. simpl. omega. 
Qed.

Remark list_length_incl:
  forall (A: Type) (l1: list A), list_norepet l1 ->
  forall l2, List.incl l1 l2 -> List.length l1 = List.length l2 -> List.incl l2 l1.
Proof.
  induction 1; simpl; intros.
  destruct l2; simpl in *. auto with coqlib. discriminate.
  exploit (List.in_split hd l2). auto with coqlib. intros [l3 [l4 EQ]]. subst l2.
  assert (incl (l3 ++ l4) tl).
    apply IHlist_norepet. red; intros. 
    exploit (H1 a); auto with coqlib. 
    repeat rewrite in_app_iff. simpl. intuition. subst. contradiction.
    repeat rewrite app_length in *. simpl in H2. omega. 
  red; simpl; intros. rewrite in_app_iff in H4; simpl in H4. intuition. 
Qed.

Remark list_strict_incl_length:
  forall (A: Type) (l1 l2: list A) (x: A),
  list_norepet l1 -> List.incl l1 l2 -> ~In x l1 -> In x l2 ->
  (List.length l1 < List.length l2)%nat.
Proof.
  intros. exploit list_incl_length; eauto. intros. 
  assert (length l1 = length l2 \/ length l1 < length l2)%nat by omega.
  destruct H4; auto. elim H1. eapply list_length_incl; eauto. 
Qed.

Remark list_norepet_map:
  forall (A B: Type) (f: A -> B) (l: list A),
  list_norepet (List.map f l) -> list_norepet l.
Proof.
  induction l; simpl; intros.
  constructor.
  inv H. constructor; auto. red; intros; elim H2. apply List.in_map; auto.
Qed.

Theorem cardinal_remove:
  forall x m y, T.get x m = Some y -> (cardinal (T.remove x m) < cardinal m)%nat.
Proof.
  unfold cardinal; intros. apply list_strict_incl_length with (x := (x, y)).
  apply list_norepet_map with (f := @fst T.elt V). apply T.elements_keys_norepet.
  red; intros. destruct a as [x' y']. exploit T.elements_complete; eauto. 
  rewrite T.grspec. destruct (T.elt_eq x' x); intros; try discriminate.
  apply T.elements_correct; auto.
  red; intros. exploit T.elements_complete; eauto. rewrite T.grspec. rewrite dec_eq_true. congruence.
  apply T.elements_correct; auto.
Qed.

End MEASURE.

(** Forall and exists *)

Section FORALL_EXISTS.

Variable A: Type.

Definition for_all (m: T.t A) (f: T.elt -> A -> bool) : bool :=
  T.fold (fun b x a => b && f x a) m true.

Lemma for_all_correct:
  forall m f,
  for_all m f = true <-> (forall x a, T.get x m = Some a -> f x a = true).
Proof.
  intros m0 f.
  unfold for_all. apply fold_rec; intros.
- (* Extensionality *)
  rewrite H0. split; intros. rewrite <- H in H2; auto. rewrite H in H2; auto. 
- (* Base case *)
  split; intros. rewrite T.gempty in H0; congruence. auto.
- (* Inductive case *)
  split; intros.
  destruct (andb_prop _ _ H2). rewrite T.gsspec in H3. destruct (T.elt_eq x k). 
  inv H3. auto.
  apply H1; auto.
  apply andb_true_intro. split. 
  rewrite H1. intros. apply H2. rewrite T.gso; auto. congruence. 
  apply H2. apply T.gss.
Qed.

Definition exists_ (m: T.t A) (f: T.elt -> A -> bool) : bool :=
  T.fold (fun b x a => b || f x a) m false.

Lemma exists_correct:
  forall m f,
  exists_ m f = true <-> (exists x a, T.get x m = Some a /\ f x a = true).
Proof.
  intros m0 f.
  unfold exists_. apply fold_rec; intros.
- (* Extensionality *)
  rewrite H0. split; intros (x0 & a0 & P & Q); exists x0; exists a0; split; auto; congruence. 
- (* Base case *)
  split; intros. congruence. destruct H as (x & a & P & Q). rewrite T.gempty in P; congruence.
- (* Inductive case *)
  split; intros.
  destruct (orb_true_elim _ _ H2).
  rewrite H1 in e. destruct e as (x1 & a1 & P & Q).
  exists x1; exists a1; split; auto. rewrite T.gso; auto. congruence.
  exists k; exists v; split; auto. apply T.gss. 
  destruct H2 as (x1 & a1 & P & Q). apply orb_true_intro.
  rewrite T.gsspec in P. destruct (T.elt_eq x1 k).
  inv P. right; auto.
  left. apply H1. exists x1; exists a1; auto.
Qed.

Remark exists_for_all:
  forall m f,
  exists_ m f = negb (for_all m (fun x a => negb (f x a))).
Proof.
  intros. unfold exists_, for_all. rewrite ! T.fold_spec. 
  change false with (negb true). generalize (T.elements m) true. 
  induction l; simpl; intros.
  auto.
  rewrite <- IHl. f_equal. 
  destruct b; destruct (f (fst a) (snd a)); reflexivity.
Qed.

Remark for_all_exists:
  forall m f,
  for_all m f = negb (exists_ m (fun x a => negb (f x a))).
Proof.
  intros. unfold exists_, for_all. rewrite ! T.fold_spec. 
  change true with (negb false). generalize (T.elements m) false. 
  induction l; simpl; intros.
  auto.
  rewrite <- IHl. f_equal. 
  destruct b; destruct (f (fst a) (snd a)); reflexivity.
Qed.

Lemma for_all_false:
  forall m f,
  for_all m f = false <-> (exists x a, T.get x m = Some a /\ f x a = false).
Proof.
  intros. rewrite for_all_exists. 
  rewrite negb_false_iff. rewrite exists_correct. 
  split; intros (x & a & P & Q); exists x; exists a; split; auto. 
  rewrite negb_true_iff in Q. auto.
  rewrite Q; auto. 
Qed.

Lemma exists_false:
  forall m f,
  exists_ m f = false <-> (forall x a, T.get x m = Some a -> f x a = false).
Proof.
  intros. rewrite exists_for_all. 
  rewrite negb_false_iff. rewrite for_all_correct.
  split; intros. apply H in H0. rewrite negb_true_iff in H0. auto. rewrite H; auto. 
Qed.

End FORALL_EXISTS.

(** More about [beq] *)

Section BOOLEAN_EQUALITY.

Variable A: Type.
Variable beqA: A -> A -> bool.

Theorem beq_false:
  forall m1 m2,
  T.beq beqA m1 m2 = false <->
  exists x, match T.get x m1, T.get x m2 with
            | None, None => False
            | Some a1, Some a2 => beqA a1 a2 = false
            | _, _ => True
            end.
Proof.
  intros; split; intros.
- (* beq = false -> existence *)
  set (p1 := fun x a1 => match T.get x m2 with None => false | Some a2 => beqA a1 a2 end).
  set (p2 := fun x a2 => match T.get x m1 with None => false | Some a1 => beqA a1 a2 end).
  destruct (for_all m1 p1) eqn:F1; [destruct (for_all m2 p2) eqn:F2 | idtac].
  + cut (T.beq beqA m1 m2 = true). congruence. 
    rewrite for_all_correct in *. rewrite T.beq_correct; intros. 
    destruct (T.get x m1) as [a1|] eqn:X1. 
    generalize (F1 _ _ X1). unfold p1. destruct (T.get x m2); congruence.
    destruct (T.get x m2) as [a2|] eqn:X2; auto.
    generalize (F2 _ _ X2). unfold p2. rewrite X1. congruence. 
  + rewrite for_all_false in F2. destruct F2 as (x & a & P & Q).
    exists x. rewrite P. unfold p2 in Q. destruct (T.get x m1); auto. 
  + rewrite for_all_false in F1. destruct F1 as (x & a & P & Q).
    exists x. rewrite P. unfold p1 in Q. destruct (T.get x m2); auto.
- (* existence -> beq = false *)
  destruct H as [x P].
  destruct (T.beq beqA m1 m2) eqn:E; auto. 
  rewrite T.beq_correct in E. 
  generalize (E x). destruct (T.get x m1); destruct (T.get x m2); tauto || congruence.
Qed.

End BOOLEAN_EQUALITY.

(** Extensional equality between trees *)

Section EXTENSIONAL_EQUALITY.

Variable A: Type.
Variable eqA: A -> A -> Prop.
Hypothesis eqAeq: Equivalence eqA.

Definition Equal (m1 m2: T.t A) : Prop :=
  forall x, match T.get x m1, T.get x m2 with
                | None, None => True
                | Some a1, Some a2 => a1 === a2
                | _, _ => False
            end.

Lemma Equal_refl: forall m, Equal m m.
Proof.
  intros; red; intros. destruct (T.get x m); auto. reflexivity. 
Qed.

Lemma Equal_sym: forall m1 m2, Equal m1 m2 -> Equal m2 m1.
Proof.
  intros; red; intros. generalize (H x). destruct (T.get x m1); destruct (T.get x m2); auto. intros; symmetry; auto.
Qed.

Lemma Equal_trans: forall m1 m2 m3, Equal m1 m2 -> Equal m2 m3 -> Equal m1 m3.
Proof.
  intros; red; intros. generalize (H x) (H0 x).
  destruct (T.get x m1); destruct (T.get x m2); try tauto;
  destruct (T.get x m3); try tauto. 
  intros. transitivity a0; auto.
Qed.

Instance Equal_Equivalence : Equivalence Equal := {
  Equivalence_Reflexive := Equal_refl;
  Equivalence_Symmetric := Equal_sym;
  Equivalence_Transitive := Equal_trans
}.

Hypothesis eqAdec: EqDec A eqA.

Program Definition Equal_dec (m1 m2: T.t A) : { m1 === m2 } + { m1 =/= m2 } :=
  match T.beq (fun a1 a2 => proj_sumbool (a1 == a2)) m1 m2 with
  | true => left _
  | false => right _
  end.
Next Obligation.
  rename Heq_anonymous into B.
  symmetry in B. rewrite T.beq_correct in B.
  red; intros. generalize (B x). 
  destruct (T.get x m1); destruct (T.get x m2); auto. 
  intros. eapply proj_sumbool_true; eauto. 
Qed.
Next Obligation.
  assert (T.beq (fun a1 a2 => proj_sumbool (a1 == a2)) m1 m2 = true).
  apply T.beq_correct; intros. 
  generalize (H x). 
  destruct (T.get x m1); destruct (T.get x m2); try tauto. 
  intros. apply proj_sumbool_is_true; auto.
  unfold equiv, complement in H0. congruence.
Qed.

Instance Equal_EqDec : EqDec (T.t A) Equal := Equal_dec.

End EXTENSIONAL_EQUALITY.

End Tree_Properties.

Module PTree_Properties := Tree_Properties(PTree).

(** * Useful notations *)

Notation "a ! b" := (PTree.get b a) (at level 1).
Notation "a !! b" := (PMap.get b a) (at level 1).

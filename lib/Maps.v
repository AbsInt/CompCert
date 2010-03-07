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

Require Import Coqlib.

Set Implicit Arguments.

(** * The abstract signatures of trees *)

Module Type TREE.
  Variable elt: Type.
  Variable elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Variable t: Type -> Type.
  Variable eq: forall (A: Type), (forall (x y: A), {x=y} + {x<>y}) ->
                forall (a b: t A), {a = b} + {a <> b}.
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
    forall (A: Type) (P: A -> A -> Prop) (cmp: A -> A -> bool),
    (forall (x y: A), cmp x y = true -> P x y) ->
    forall (t1 t2: t A), beq cmp t1 t2 = true ->
    forall (x: elt),
    match get x t1, get x t2 with
    | None, None => True
    | Some y1, Some y2 => P y1 y2
    | _, _ => False
    end.

  (** Applying a function to all data of a tree. *)
  Variable map:
    forall (A B: Type), (elt -> A -> B) -> t A -> t B.
  Hypothesis gmap:
    forall (A B: Type) (f: elt -> A -> B) (i: elt) (m: t A),
    get i (map f m) = option_map (f i) (get i m).

  (** Applying a function pairwise to all data of two trees. *)
  Variable combine:
    forall (A: Type), (option A -> option A -> option A) -> t A -> t A -> t A.
  Hypothesis gcombine:
    forall (A: Type) (f: option A -> option A -> option A),
    f None None = None ->
    forall (m1 m2: t A) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).
  Hypothesis combine_commut:
    forall (A: Type) (f g: option A -> option A -> option A),
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
  Hypothesis elements_canonical_order:
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
    (forall i x, get i m = Some x -> exists y, get i n = Some y /\ R x y) ->
    (forall i y, get i n = Some y -> exists x, get i m = Some x /\ R x y) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (elements m) (elements n).
  Hypothesis elements_extensional:
    forall (A: Type) (m n: t A),
    (forall i, get i m = get i n) ->
    elements m = elements n.

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
    | Node : tree A -> option A -> tree A -> tree A
  .
  Implicit Arguments Leaf [A].
  Implicit Arguments Node [A].

  Definition t := tree.

  Theorem eq : forall (A : Type),
    (forall (x y: A), {x=y} + {x<>y}) ->
    forall (a b : t A), {a = b} + {a <> b}.
  Proof.
    intros A eqA.
    decide equality.
    generalize o o0; decide equality.
  Qed.

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

  Section EXTENSIONAL_EQUALITY.

    Variable A: Type.
    Variable eqA: A -> A -> Prop.
    Variable beqA: A -> A -> bool.
    Hypothesis beqA_correct: forall x y, beqA x y = true -> eqA x y.

    Definition exteq (m1 m2: t A) : Prop :=
      forall (x: elt),
      match get x m1, get x m2 with
      | None, None => True
      | Some y1, Some y2 => eqA y1 y2
      | _, _ => False
      end.

    Fixpoint bempty (m: t A) : bool :=
      match m with
      | Leaf => true
      | Node l None r => bempty l && bempty r
      | Node l (Some _) r => false
      end.

    Lemma bempty_correct:
      forall m, bempty m = true -> forall x, get x m = None.
    Proof.
      induction m; simpl; intros. 
      change (@Leaf A) with (empty A). apply gempty.
      destruct o. congruence. destruct (andb_prop _ _ H). 
      destruct x; simpl; auto.
    Qed.

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

    Lemma beq_correct:
      forall m1 m2, beq m1 m2 = true -> exteq m1 m2.
    Proof.
      induction m1; destruct m2; simpl.
      intros; red; intros. change (@Leaf A) with (empty A). 
      repeat rewrite gempty. auto.
      destruct o; intro. congruence. 
      red; intros. change (@Leaf A) with (empty A). rewrite gempty.
      rewrite bempty_correct. auto. assumption. 
      destruct o; intro. congruence. 
      red; intros. change (@Leaf A) with (empty A). rewrite gempty.
      rewrite bempty_correct. auto. assumption. 
      destruct o; destruct o0; simpl; intro; try congruence.
      destruct (andb_prop _ _ H). destruct (andb_prop _ _ H0). 
      red; intros. destruct x; simpl.
      apply IHm1_2; auto. apply IHm1_1; auto. 
      apply beqA_correct; auto. 
      destruct (andb_prop _ _ H).
      red; intros. destruct x; simpl.
      apply IHm1_2; auto. apply IHm1_1; auto.
      auto.
    Qed.

  End EXTENSIONAL_EQUALITY.

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

  Section COMBINE.

  Variable A: Type.
  Variable f: option A -> option A -> option A.
  Hypothesis f_none_none: f None None = None.

  Fixpoint xcombine_l (m : t A) {struct m} : t A :=
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

  Fixpoint xcombine_r (m : t A) {struct m} : t A :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node' (xcombine_r l) (f None o) (xcombine_r r)
      end.

  Lemma xgcombine_r :
          forall (m: t A) (i : positive),
          get i (xcombine_r m) = f None (get i m).
    Proof.
      induction m; intros; simpl.
      repeat rewrite gleaf. auto.
      rewrite gnode'. destruct i; simpl; auto.
    Qed.

  Fixpoint combine (m1 m2 : t A) {struct m1} : t A :=
    match m1 with
    | Leaf => xcombine_r m2
    | Node l1 o1 r1 =>
        match m2 with
        | Leaf => xcombine_l m1
        | Node l2 o2 r2 => Node' (combine l1 l2) (f o1 o2) (combine r1 r2)
        end
    end.

  Theorem gcombine:
      forall (m1 m2: t A) (i: positive),
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
    forall (A : Type) (f g : option A -> option A -> option A) (m : t A),
    (forall (i j : option A), f i j = g j i) ->
    xcombine_l f m = xcombine_r g m.
    Proof.
      induction m; intros; simpl; auto.
      rewrite IHm1; auto.
      rewrite IHm2; auto.
      rewrite H; auto.
    Qed.

  Theorem combine_commut:
    forall (A: Type) (f g: option A -> option A -> option A),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.
  Proof.
    intros A f g EQ1.
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

    Fixpoint xelements (A : Type) (m : t A) (i : positive) {struct m}
             : list (positive * A) :=
      match m with
      | Leaf => nil
      | Node l None r =>
          (xelements l (append i (xO xH))) ++ (xelements r (append i (xI xH)))
      | Node l (Some x) r =>
          (xelements l (append i (xO xH)))
          ++ ((i, x) :: xelements r (append i (xI xH)))
      end.

  (* Note: function [xelements] above is inefficient.  We should apply
     deforestation to it, but that makes the proofs even harder. *)

  Definition elements A (m : t A) := xelements m xH.

    Lemma xelements_correct:
      forall (A: Type) (m: t A) (i j : positive) (v: A),
      get i m = Some v -> In (append j i, v) (xelements m j).
    Proof.
      induction m; intros.
       rewrite (gleaf A i) in H; congruence.
       destruct o; destruct i; simpl; simpl in H.
        rewrite append_assoc_1; apply in_or_app; right; apply in_cons;
          apply IHm2; auto.
        rewrite append_assoc_0; apply in_or_app; left; apply IHm1; auto.
        rewrite append_neutral_r; apply in_or_app; injection H;
          intro EQ; rewrite EQ; right; apply in_eq.
        rewrite append_assoc_1; apply in_or_app; right; apply IHm2; auto.
        rewrite append_assoc_0; apply in_or_app; left; apply IHm1; auto.
        congruence.
    Qed.

  Theorem elements_correct:
    forall (A: Type) (m: t A) (i: positive) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Proof.
    intros A m i v H.
    exact (xelements_correct m i xH H).
  Qed.

    Fixpoint xget (A : Type) (i j : positive) (m : t A) {struct j} : option A :=
      match i, j with
      | _, xH => get i m
      | xO ii, xO jj => xget ii jj m
      | xI ii, xI jj => xget ii jj m
      | _, _ => None
      end.

    Lemma xget_left :
      forall (A : Type) (j i : positive) (m1 m2 : t A) (o : option A) (v : A),
      xget i (append j (xO xH)) m1 = Some v -> xget i j (Node m1 o m2) = Some v.
    Proof.
      induction j; intros; destruct i; simpl; simpl in H; auto; try congruence.
      destruct i; congruence.
    Qed.

    Lemma xelements_ii :
      forall (A: Type) (m: t A) (i j : positive) (v: A),
      In (xI i, v) (xelements m (xI j)) -> In (i, v) (xelements m j).
    Proof.
      induction m.
       simpl; auto.
       intros; destruct o; simpl; simpl in H; destruct (in_app_or _ _ _ H);
         apply in_or_app.
        left; apply IHm1; auto.
        right; destruct (in_inv H0).
         injection H1; intros EQ1 EQ2; rewrite EQ1; rewrite EQ2; apply in_eq.
         apply in_cons; apply IHm2; auto.
        left; apply IHm1; auto.
        right; apply IHm2; auto.
    Qed.

    Lemma xelements_io :
      forall (A: Type) (m: t A) (i j : positive) (v: A),
      ~In (xI i, v) (xelements m (xO j)).
    Proof.
      induction m.
       simpl; auto.
       intros; destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
        apply (IHm1 _ _ _ H0).
        destruct (in_inv H0).
         congruence.
         apply (IHm2 _ _ _ H1).
        apply (IHm1 _ _ _ H0).
        apply (IHm2 _ _ _ H0).
    Qed.

    Lemma xelements_oo :
      forall (A: Type) (m: t A) (i j : positive) (v: A),
      In (xO i, v) (xelements m (xO j)) -> In (i, v) (xelements m j).
    Proof.
      induction m.
       simpl; auto.
       intros; destruct o; simpl; simpl in H; destruct (in_app_or _ _ _ H);
         apply in_or_app.
        left; apply IHm1; auto.
        right; destruct (in_inv H0).
         injection H1; intros EQ1 EQ2; rewrite EQ1; rewrite EQ2; apply in_eq.
         apply in_cons; apply IHm2; auto.
        left; apply IHm1; auto.
        right; apply IHm2; auto.
    Qed.

    Lemma xelements_oi :
      forall (A: Type) (m: t A) (i j : positive) (v: A),
      ~In (xO i, v) (xelements m (xI j)).
    Proof.
      induction m.
       simpl; auto.
       intros; destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
        apply (IHm1 _ _ _ H0).
        destruct (in_inv H0).
         congruence.
         apply (IHm2 _ _ _ H1).
        apply (IHm1 _ _ _ H0).
        apply (IHm2 _ _ _ H0).
    Qed.

    Lemma xelements_ih :
      forall (A: Type) (m1 m2: t A) (o: option A) (i : positive) (v: A),
      In (xI i, v) (xelements (Node m1 o m2) xH) -> In (i, v) (xelements m2 xH).
    Proof.
      destruct o; simpl; intros; destruct (in_app_or _ _ _ H).
        absurd (In (xI i, v) (xelements m1 2)); auto; apply xelements_io; auto.
        destruct (in_inv H0).
         congruence.
         apply xelements_ii; auto.
        absurd (In (xI i, v) (xelements m1 2)); auto; apply xelements_io; auto.
        apply xelements_ii; auto.
    Qed.

    Lemma xelements_oh :
      forall (A: Type) (m1 m2: t A) (o: option A) (i : positive) (v: A),
      In (xO i, v) (xelements (Node m1 o m2) xH) -> In (i, v) (xelements m1 xH).
    Proof.
      destruct o; simpl; intros; destruct (in_app_or _ _ _ H).
        apply xelements_oo; auto.
        destruct (in_inv H0).
         congruence.
         absurd (In (xO i, v) (xelements m2 3)); auto; apply xelements_oi; auto.
        apply xelements_oo; auto.
        absurd (In (xO i, v) (xelements m2 3)); auto; apply xelements_oi; auto.
    Qed.

    Lemma xelements_hi :
      forall (A: Type) (m: t A) (i : positive) (v: A),
      ~In (xH, v) (xelements m (xI i)).
    Proof.
      induction m; intros.
       simpl; auto.
       destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
        generalize H0; apply IHm1; auto.
        destruct (in_inv H0).
         congruence.
         generalize H1; apply IHm2; auto.
        generalize H0; apply IHm1; auto.
        generalize H0; apply IHm2; auto.
    Qed.

    Lemma xelements_ho :
      forall (A: Type) (m: t A) (i : positive) (v: A),
      ~In (xH, v) (xelements m (xO i)).
    Proof.
      induction m; intros.
       simpl; auto.
       destruct o; simpl; intro H; destruct (in_app_or _ _ _ H).
        generalize H0; apply IHm1; auto.
        destruct (in_inv H0).
         congruence.
         generalize H1; apply IHm2; auto.
        generalize H0; apply IHm1; auto.
        generalize H0; apply IHm2; auto.
    Qed.

    Lemma get_xget_h :
      forall (A: Type) (m: t A) (i: positive), get i m = xget i xH m.
    Proof.
      destruct i; simpl; auto.
    Qed.

    Lemma xelements_complete:
      forall (A: Type) (i j : positive) (m: t A) (v: A),
      In (i, v) (xelements m j) -> xget i j m = Some v.
    Proof.
      induction i; simpl; intros; destruct j; simpl.
       apply IHi; apply xelements_ii; auto.
       absurd (In (xI i, v) (xelements m (xO j))); auto; apply xelements_io.
       destruct m.
        simpl in H; tauto.
        rewrite get_xget_h. apply IHi. apply (xelements_ih _ _ _ _ _ H).
       absurd (In (xO i, v) (xelements m (xI j))); auto; apply xelements_oi.
       apply IHi; apply xelements_oo; auto.
       destruct m.
        simpl in H; tauto.
        rewrite get_xget_h. apply IHi. apply (xelements_oh _ _ _ _ _ H).
       absurd (In (xH, v) (xelements m (xI j))); auto; apply xelements_hi.
       absurd (In (xH, v) (xelements m (xO j))); auto; apply xelements_ho.
       destruct m.
        simpl in H; tauto.
        destruct o; simpl in H; destruct (in_app_or _ _ _ H).
         absurd (In (xH, v) (xelements m1 (xO xH))); auto; apply xelements_ho.
         destruct (in_inv H0).
          congruence.
          absurd (In (xH, v) (xelements m2 (xI xH))); auto; apply xelements_hi.
         absurd (In (xH, v) (xelements m1 (xO xH))); auto; apply xelements_ho.
         absurd (In (xH, v) (xelements m2 (xI xH))); auto; apply xelements_hi.
    Qed.

  Theorem elements_complete:
    forall (A: Type) (m: t A) (i: positive) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Proof.
    intros A m i v H.
    unfold elements in H.
    rewrite get_xget_h.
    exact (xelements_complete i xH m v H).
  Qed.

  Lemma in_xelements:
    forall (A: Type) (m: t A) (i k: positive) (v: A),
    In (k, v) (xelements m i) ->
    exists j, k = append i j.
  Proof.
    induction m; simpl; intros.
    tauto.
    assert (k = i \/ In (k, v) (xelements m1 (append i 2))
                  \/ In (k, v) (xelements m2 (append i 3))).
      destruct o.
      elim (in_app_or _ _ _ H); simpl; intuition.
      replace k with i. tauto. congruence.
      elim (in_app_or _ _ _ H); simpl; intuition.
    elim H0; intro.
    exists xH. rewrite append_neutral_r. auto.
    elim H1; intro.
    elim (IHm1 _ _ _ H2). intros k1 EQ. rewrite EQ.
    rewrite <- append_assoc_0. exists (xO k1); auto.
    elim (IHm2 _ _ _ H2). intros k1 EQ. rewrite EQ.
    rewrite <- append_assoc_1. exists (xI k1); auto.
  Qed.

  Definition xkeys (A: Type) (m: t A) (i: positive) :=
    List.map (@fst positive A) (xelements m i).

  Lemma in_xkeys:
    forall (A: Type) (m: t A) (i k: positive),
    In k (xkeys m i) ->
    exists j, k = append i j.
  Proof.
    unfold xkeys; intros. 
    elim (list_in_map_inv _ _ _ H). intros [k1 v1] [EQ IN].
    simpl in EQ; subst k1. apply in_xelements with A m v1. auto.
  Qed.

  Remark list_append_cons_norepet:
    forall (A: Type) (l1 l2: list A) (x: A),
    list_norepet l1 -> list_norepet l2 -> list_disjoint l1 l2 ->
    ~In x l1 -> ~In x l2 ->
    list_norepet (l1 ++ x :: l2).
  Proof.
    intros. apply list_norepet_append_commut. simpl; constructor.
    red; intros. elim (in_app_or _ _ _ H4); intro; tauto.
    apply list_norepet_append; auto. 
    apply list_disjoint_sym; auto.
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
    forall (A: Type) (m: t A) (i: positive),
    list_norepet (xkeys m i).
  Proof.
    induction m; unfold xkeys; simpl; fold xkeys; intros.
    constructor.
    assert (list_disjoint (xkeys m1 (append i 2)) (xkeys m2 (append i 3))).
      red; intros; red; intro. subst y. 
      elim (in_xkeys _ _ _ H); intros j1 EQ1.
      elim (in_xkeys _ _ _ H0); intros j2 EQ2.
      rewrite EQ1 in EQ2. 
      rewrite <- append_assoc_0 in EQ2. 
      rewrite <- append_assoc_1 in EQ2. 
      generalize (append_injective _ _ _ EQ2). congruence.
    assert (forall (m: t A) j,
            j = 2%positive \/ j = 3%positive ->
            ~In i (xkeys m (append i j))).
      intros; red; intros. 
      elim (in_xkeys _ _ _ H1); intros k EQ.
      assert (EQ1: append i xH = append (append i j) k).
        rewrite append_neutral_r. auto.
      elim H0; intro; subst j;
      try (rewrite <- append_assoc_0 in EQ1);
      try (rewrite <- append_assoc_1 in EQ1);
      generalize (append_injective _ _ _ EQ1); congruence.
    destruct o; rewrite list_append_map; simpl;
    change (List.map (@fst positive A) (xelements m1 (append i 2)))
      with (xkeys m1 (append i 2));
    change (List.map (@fst positive A) (xelements m2 (append i 3)))
      with (xkeys m2 (append i 3)).
    apply list_append_cons_norepet; auto. 
    apply list_norepet_append; auto.
  Qed.

  Theorem elements_keys_norepet:
    forall (A: Type) (m: t A), 
    list_norepet (List.map (@fst elt A) (elements m)).
  Proof.
    intros. change (list_norepet (xkeys m 1)). apply xelements_keys_norepet.
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
    assert (forall m n j,
    (forall i x, get i m = Some x -> exists y, get i n = Some y /\ R x y) ->
    (forall i y, get i n = Some y -> exists x, get i m = Some x /\ R x y) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (xelements m j) (xelements n j)).
    induction m; induction n; intros; simpl.
    constructor.
    destruct o. exploit (H0 xH). simpl. reflexivity. simpl. intros [x [P Q]]. congruence.
    change (@nil (positive*A)) with ((@nil (positive * A))++nil).
    apply list_forall2_app.
    apply IHn1.
    intros. rewrite gleaf in H1. congruence.
    intros. exploit (H0 (xO i)). simpl; eauto. rewrite gleaf. intros [x [P Q]]. congruence.
    apply IHn2.
    intros. rewrite gleaf in H1. congruence.
    intros. exploit (H0 (xI i)). simpl; eauto. rewrite gleaf. intros [x [P Q]]. congruence.
    destruct o. exploit (H xH). simpl. reflexivity. simpl. intros [x [P Q]]. congruence.
    change (@nil (positive*B)) with (xelements (@Leaf B) (append j 2) ++ (xelements (@Leaf B) (append j 3))).
    apply list_forall2_app.
    apply IHm1.
    intros. exploit (H (xO i)). simpl; eauto. rewrite gleaf. intros [y [P Q]]. congruence.
    intros. rewrite gleaf in H1. congruence.
    apply IHm2.
    intros. exploit (H (xI i)). simpl; eauto. rewrite gleaf. intros [y [P Q]]. congruence.
    intros. rewrite gleaf in H1. congruence.
    exploit (IHm1 n1 (append j 2)). 
    intros. exploit (H (xO i)). simpl; eauto. simpl. auto.
    intros. exploit (H0 (xO i)). simpl; eauto. simpl; auto.
    intro REC1.
    exploit (IHm2 n2 (append j 3)). 
    intros. exploit (H (xI i)). simpl; eauto. simpl. auto.
    intros. exploit (H0 (xI i)). simpl; eauto. simpl; auto.
    intro REC2.
    destruct o; destruct o0.
    apply list_forall2_app; auto. constructor; auto. 
    simpl; split; auto. exploit (H xH). simpl; eauto. simpl. intros [y [P Q]]. congruence.
    exploit (H xH). simpl; eauto. simpl. intros [y [P Q]]; congruence.
    exploit (H0 xH). simpl; eauto. simpl. intros [x [P Q]]; congruence.
    apply list_forall2_app; auto.

    unfold elements; auto.
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

(*
  Definition fold (A B : Type) (f: B -> positive -> A -> B) (tr: t A) (v: B) :=
     List.fold_left (fun a p => f a (fst p) (snd p)) (elements tr) v.
*)

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
    forall (A B: Type) (f: B -> positive -> A -> B) m i v,
    xfold f i m v =
    List.fold_left (fun a p => f a (fst p) (snd p))
                   (xelements m i)
                   v.
  Proof.
    induction m; intros.
    simpl. auto.
    simpl. destruct o.
    rewrite fold_left_app. simpl. 
    rewrite IHm1. apply IHm2. 
    rewrite fold_left_app. simpl.
    rewrite IHm1. apply IHm2.
  Qed.

  Theorem fold_spec:
    forall (A B: Type) (f: B -> positive -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  Proof.
    intros. unfold fold, elements. apply xfold_xelements. 
  Qed.

End PTree.

(** * An implementation of maps over type [positive] *)

Module PMap <: MAP.
  Definition elt := positive.
  Definition elt_eq := peq.

  Definition t (A : Type) : Type := (A * PTree.t A)%type.

  Definition eq: forall (A: Type), (forall (x y: A), {x=y} + {x<>y}) ->
                 forall (a b: t A), {a = b} + {a <> b}.
  Proof.
    intros. 
    generalize (PTree.eq X). intros. 
    decide equality.
  Qed.

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
    (f (fst m), PTree.map (fun _ => f) (snd m)).

  Theorem gmap:
    forall (A B: Type) (f: A -> B) (i: positive) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold map. unfold get. simpl. rewrite PTree.gmap.
    unfold option_map. destruct (PTree.get i (snd m)); auto.
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
  Definition eq: forall (A: Type), (forall (x y: A), {x=y} + {x<>y}) ->
                 forall (a b: t A), {a = b} + {a <> b} := PMap.eq.
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

Definition f' (a: A) (p : T.elt * V) := f a (fst p) (snd p).

Definition P' (l: list (T.elt * V)) (a: A) : Prop :=
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

End Tree_Properties.

Module PTree_Properties := Tree_Properties(PTree).

(** * Useful notations *)

Notation "a ! b" := (PTree.get b a) (at level 1).
Notation "a !! b" := (PMap.get b a) (at level 1).

(* $Id: Maps.v,v 1.12.4.4 2006/01/07 11:46:55 xleroy Exp $ *)

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
  Variable elt: Set.
  Variable elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Variable t: Set -> Set.
  Variable eq: forall (A: Set), (forall (x y: A), {x=y} + {x<>y}) ->
                forall (a b: t A), {a = b} + {a <> b}.
  Variable empty: forall (A: Set), t A.
  Variable get: forall (A: Set), elt -> t A -> option A.
  Variable set: forall (A: Set), elt -> A -> t A -> t A.
  Variable remove: forall (A: Set), elt -> t A -> t A.

  (** The ``good variables'' properties for trees, expressing
    commutations between [get], [set] and [remove]. *)
  Hypothesis gempty:
    forall (A: Set) (i: elt), get i (empty A) = None.
  Hypothesis gss:
    forall (A: Set) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Hypothesis gso:
    forall (A: Set) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Hypothesis gsspec:
    forall (A: Set) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Hypothesis gsident:
    forall (A: Set) (i: elt) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.
  (* We could implement the following, but it's not needed for the moment.
    Hypothesis grident:
      forall (A: Set) (i: elt) (m: t A) (v: A),
      get i m = None -> remove i m = m.
  *)
  Hypothesis grs:
    forall (A: Set) (i: elt) (m: t A), get i (remove i m) = None.
  Hypothesis gro:
    forall (A: Set) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.

  (** Extensional equality between trees. *)
  Variable beq: forall (A: Set), (A -> A -> bool) -> t A -> t A -> bool.
  Hypothesis beq_correct:
    forall (A: Set) (P: A -> A -> Prop) (cmp: A -> A -> bool),
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
    forall (A B: Set), (elt -> A -> B) -> t A -> t B.
  Hypothesis gmap:
    forall (A B: Set) (f: elt -> A -> B) (i: elt) (m: t A),
    get i (map f m) = option_map (f i) (get i m).

  (** Applying a function pairwise to all data of two trees. *)
  Variable combine:
    forall (A: Set), (option A -> option A -> option A) -> t A -> t A -> t A.
  Hypothesis gcombine:
    forall (A: Set) (f: option A -> option A -> option A)
           (m1 m2: t A) (i: elt),
    f None None = None ->
    get i (combine f m1 m2) = f (get i m1) (get i m2).
  Hypothesis combine_commut:
    forall (A: Set) (f g: option A -> option A -> option A),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.

  (** Enumerating the bindings of a tree. *)
  Variable elements:
    forall (A: Set), t A -> list (elt * A).
  Hypothesis elements_correct:
    forall (A: Set) (m: t A) (i: elt) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Hypothesis elements_complete:
    forall (A: Set) (m: t A) (i: elt) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Hypothesis elements_keys_norepet:
    forall (A: Set) (m: t A), 
    list_norepet (List.map (@fst elt A) (elements m)).

  (** Folding a function over all bindings of a tree. *)
  Variable fold:
    forall (A B: Set), (B -> elt -> A -> B) -> t A -> B -> B.
  Hypothesis fold_spec:
    forall (A B: Set) (f: B -> elt -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
End TREE.

(** * The abstract signatures of maps *)

Module Type MAP.
  Variable elt: Set.
  Variable elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Variable t: Set -> Set.
  Variable init: forall (A: Set), A -> t A.
  Variable get: forall (A: Set), elt -> t A -> A.
  Variable set: forall (A: Set), elt -> A -> t A -> t A.
  Hypothesis gi:
    forall (A: Set) (i: elt) (x: A), get i (init x) = x.
  Hypothesis gss:
    forall (A: Set) (i: elt) (x: A) (m: t A), get i (set i x m) = x.
  Hypothesis gso:
    forall (A: Set) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Hypothesis gsspec:
    forall (A: Set) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Hypothesis gsident:
    forall (A: Set) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.
  Variable map: forall (A B: Set), (A -> B) -> t A -> t B.
  Hypothesis gmap:
    forall (A B: Set) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
End MAP.

(** * An implementation of trees over type [positive] *)

Module PTree <: TREE.
  Definition elt := positive.
  Definition elt_eq := peq.

  Inductive tree (A : Set) : Set :=
    | Leaf : tree A
    | Node : tree A -> option A -> tree A -> tree A
  .
  Implicit Arguments Leaf [A].
  Implicit Arguments Node [A].

  Definition t := tree.

  Theorem eq : forall (A : Set),
    (forall (x y: A), {x=y} + {x<>y}) ->
    forall (a b : t A), {a = b} + {a <> b}.
  Proof.
    intros A eqA.
    decide equality.
    generalize o o0; decide equality.
  Qed.

  Definition empty (A : Set) := (Leaf : t A).

  Fixpoint get (A : Set) (i : positive) (m : t A) {struct i} : option A :=
    match m with
    | Leaf => None
    | Node l o r =>
        match i with
        | xH => o
        | xO ii => get ii l
        | xI ii => get ii r
        end
    end.

  Fixpoint set (A : Set) (i : positive) (v : A) (m : t A) {struct i} : t A :=
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

  Fixpoint remove (A : Set) (i : positive) (m : t A) {struct i} : t A :=
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
    forall (A: Set) (i: positive), get i (empty A) = None.
  Proof.
    induction i; simpl; auto.
  Qed.

  Theorem gss:
    forall (A: Set) (i: positive) (x: A) (m: t A), get i (set i x m) = Some x.
  Proof.
    induction i; destruct m; simpl; auto.
  Qed.

    Lemma gleaf : forall (A : Set) (i : positive), get i (Leaf : t A) = None.
    Proof. exact gempty. Qed.

  Theorem gso:
    forall (A: Set) (i j: positive) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    induction i; intros; destruct j; destruct m; simpl;
       try rewrite <- (gleaf A i); auto; try apply IHi; congruence.
  Qed.

  Theorem gsspec:
    forall (A: Set) (i j: positive) (x: A) (m: t A),
    get i (set j x m) = if peq i j then Some x else get i m.
  Proof.
    intros.
    destruct (peq i j); [ rewrite e; apply gss | apply gso; auto ].
  Qed.

  Theorem gsident:
    forall (A: Set) (i: positive) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.
  Proof.
    induction i; intros; destruct m; simpl; simpl in H; try congruence.
     rewrite (IHi m2 v H); congruence.
     rewrite (IHi m1 v H); congruence.
  Qed.

    Lemma rleaf : forall (A : Set) (i : positive), remove i (Leaf : t A) = Leaf.
    Proof. destruct i; simpl; auto. Qed.

  Theorem grs:
    forall (A: Set) (i: positive) (m: t A), get i (remove i m) = None.
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
    forall (A: Set) (i j: positive) (m: t A),
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

  Section EXTENSIONAL_EQUALITY.

    Variable A: Set.
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

    Fixpoint xmap (A B : Set) (f : positive -> A -> B) (m : t A) (i : positive)
             {struct m} : t B :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node (xmap f l (append i (xO xH)))
                           (option_map (f i) o)
                           (xmap f r (append i (xI xH)))
      end.

  Definition map (A B : Set) (f : positive -> A -> B) m := xmap f m xH.

    Lemma xgmap:
      forall (A B: Set) (f: positive -> A -> B) (i j : positive) (m: t A),
      get i (xmap f m j) = option_map (f (append j i)) (get i m).
    Proof.
      induction i; intros; destruct m; simpl; auto.
      rewrite (append_assoc_1 j i); apply IHi.
      rewrite (append_assoc_0 j i); apply IHi.
      rewrite (append_neutral_r j); auto.
    Qed.

  Theorem gmap:
    forall (A B: Set) (f: positive -> A -> B) (i: positive) (m: t A),
    get i (map f m) = option_map (f i) (get i m).
  Proof.
    intros.
    unfold map.
    replace (f i) with (f (append xH i)).
    apply xgmap.
    rewrite append_neutral_l; auto.
  Qed.

    Fixpoint xcombine_l (A : Set) (f : option A -> option A -> option A)
                       (m : t A) {struct m} : t A :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node (xcombine_l f l) (f o None) (xcombine_l f r)
      end.

    Lemma xgcombine_l :
          forall (A : Set) (f : option A -> option A -> option A)
                 (i : positive) (m : t A),
          f None None = None -> get i (xcombine_l f m) = f (get i m) None.
    Proof.
      induction i; intros; destruct m; simpl; auto.
    Qed.

    Fixpoint xcombine_r (A : Set) (f : option A -> option A -> option A)
                       (m : t A) {struct m} : t A :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node (xcombine_r f l) (f None o) (xcombine_r f r)
      end.

    Lemma xgcombine_r :
          forall (A : Set) (f : option A -> option A -> option A)
                 (i : positive) (m : t A),
          f None None = None -> get i (xcombine_r f m) = f None (get i m).
    Proof.
      induction i; intros; destruct m; simpl; auto.
    Qed.

  Fixpoint combine (A : Set) (f : option A -> option A -> option A)
                   (m1 m2 : t A) {struct m1} : t A :=
    match m1 with
    | Leaf => xcombine_r f m2
    | Node l1 o1 r1 =>
        match m2 with
        | Leaf => xcombine_l f m1
        | Node l2 o2 r2 => Node (combine f l1 l2) (f o1 o2) (combine f r1 r2)
        end
    end.

    Lemma xgcombine:
      forall (A: Set) (f: option A -> option A -> option A) (i: positive)
             (m1 m2: t A),
      f None None = None ->
      get i (combine f m1 m2) = f (get i m1) (get i m2).
    Proof.
      induction i; intros; destruct m1; destruct m2; simpl; auto;
      try apply xgcombine_r; try apply xgcombine_l; auto.
    Qed.

  Theorem gcombine:
    forall (A: Set) (f: option A -> option A -> option A)
           (m1 m2: t A) (i: positive),
    f None None = None ->
    get i (combine f m1 m2) = f (get i m1) (get i m2).
  Proof.
    intros A f m1 m2 i H; exact (xgcombine f i m1 m2 H).
  Qed.

    Lemma xcombine_lr :
      forall (A : Set) (f g : option A -> option A -> option A) (m : t A),
      (forall (i j : option A), f i j = g j i) ->
      xcombine_l f m = xcombine_r g m.
    Proof.
      induction m; intros; simpl; auto.
      rewrite IHm1; auto.
      rewrite IHm2; auto.
      rewrite H; auto.
    Qed.

  Theorem combine_commut:
    forall (A: Set) (f g: option A -> option A -> option A),
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

    Fixpoint xelements (A : Set) (m : t A) (i : positive) {struct m}
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
      forall (A: Set) (m: t A) (i j : positive) (v: A),
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
    forall (A: Set) (m: t A) (i: positive) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Proof.
    intros A m i v H.
    exact (xelements_correct m i xH H).
  Qed.

    Fixpoint xget (A : Set) (i j : positive) (m : t A) {struct j} : option A :=
      match i, j with
      | _, xH => get i m
      | xO ii, xO jj => xget ii jj m
      | xI ii, xI jj => xget ii jj m
      | _, _ => None
      end.

    Lemma xget_left :
      forall (A : Set) (j i : positive) (m1 m2 : t A) (o : option A) (v : A),
      xget i (append j (xO xH)) m1 = Some v -> xget i j (Node m1 o m2) = Some v.
    Proof.
      induction j; intros; destruct i; simpl; simpl in H; auto; try congruence.
      destruct i; congruence.
    Qed.

    Lemma xelements_ii :
      forall (A: Set) (m: t A) (i j : positive) (v: A),
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
      forall (A: Set) (m: t A) (i j : positive) (v: A),
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
      forall (A: Set) (m: t A) (i j : positive) (v: A),
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
      forall (A: Set) (m: t A) (i j : positive) (v: A),
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
      forall (A: Set) (m1 m2: t A) (o: option A) (i : positive) (v: A),
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
      forall (A: Set) (m1 m2: t A) (o: option A) (i : positive) (v: A),
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
      forall (A: Set) (m: t A) (i : positive) (v: A),
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
      forall (A: Set) (m: t A) (i : positive) (v: A),
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
      forall (A: Set) (m: t A) (i: positive), get i m = xget i xH m.
    Proof.
      destruct i; simpl; auto.
    Qed.

    Lemma xelements_complete:
      forall (A: Set) (i j : positive) (m: t A) (v: A),
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
    forall (A: Set) (m: t A) (i: positive) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Proof.
    intros A m i v H.
    unfold elements in H.
    rewrite get_xget_h.
    exact (xelements_complete i xH m v H).
  Qed.

  Lemma in_xelements:
    forall (A: Set) (m: t A) (i k: positive) (v: A),
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

  Definition xkeys (A: Set) (m: t A) (i: positive) :=
    List.map (@fst positive A) (xelements m i).

  Lemma in_xkeys:
    forall (A: Set) (m: t A) (i k: positive),
    In k (xkeys m i) ->
    exists j, k = append i j.
  Proof.
    unfold xkeys; intros. 
    elim (list_in_map_inv _ _ _ H). intros [k1 v1] [EQ IN].
    simpl in EQ; subst k1. apply in_xelements with A m v1. auto.
  Qed.

  Remark list_append_cons_norepet:
    forall (A: Set) (l1 l2: list A) (x: A),
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
    forall (A: Set) (m: t A) (i: positive),
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
    forall (A: Set) (m: t A), 
    list_norepet (List.map (@fst elt A) (elements m)).
  Proof.
    intros. change (list_norepet (xkeys m 1)). apply xelements_keys_norepet.
  Qed.

  Definition fold (A B : Set) (f: B -> positive -> A -> B) (tr: t A) (v: B) :=
     List.fold_left (fun a p => f a (fst p) (snd p)) (elements tr) v.

  Theorem fold_spec:
    forall (A B: Set) (f: B -> positive -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  Proof.
    intros; unfold fold; auto.
  Qed.

End PTree.

(** * An implementation of maps over type [positive] *)

Module PMap <: MAP.
  Definition elt := positive.
  Definition elt_eq := peq.

  Definition t (A : Set) : Set := (A * PTree.t A)%type.

  Definition eq: forall (A: Set), (forall (x y: A), {x=y} + {x<>y}) ->
                 forall (a b: t A), {a = b} + {a <> b}.
  Proof.
    intros. 
    generalize (PTree.eq H). intros. 
    decide equality.
  Qed.

  Definition init (A : Set) (x : A) :=
    (x, PTree.empty A).

  Definition get (A : Set) (i : positive) (m : t A) :=
    match PTree.get i (snd m) with
    | Some x => x
    | None => fst m
    end.

  Definition set (A : Set) (i : positive) (x : A) (m : t A) :=
    (fst m, PTree.set i x (snd m)).

  Theorem gi:
    forall (A: Set) (i: positive) (x: A), get i (init x) = x.
  Proof.
    intros. unfold init. unfold get. simpl. rewrite PTree.gempty. auto.
  Qed.

  Theorem gss:
    forall (A: Set) (i: positive) (x: A) (m: t A), get i (set i x m) = x.
  Proof.
    intros. unfold get. unfold set. simpl. rewrite PTree.gss. auto.
  Qed.

  Theorem gso:
    forall (A: Set) (i j: positive) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. unfold get. unfold set. simpl. rewrite PTree.gso; auto.
  Qed.

  Theorem gsspec:
    forall (A: Set) (i j: positive) (x: A) (m: t A),
    get i (set j x m) = if peq i j then x else get i m.
  Proof.
    intros. destruct (peq i j).
     rewrite e. apply gss. auto.
     apply gso. auto.
  Qed.

  Theorem gsident:
    forall (A: Set) (i j: positive) (m: t A),
    get j (set i (get i m) m) = get j m.
  Proof.
    intros. destruct (peq i j).
     rewrite e. rewrite gss. auto.
     rewrite gso; auto.
  Qed.

  Definition map (A B : Set) (f : A -> B) (m : t A) : t B :=
    (f (fst m), PTree.map (fun _ => f) (snd m)).

  Theorem gmap:
    forall (A B: Set) (f: A -> B) (i: positive) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold map. unfold get. simpl. rewrite PTree.gmap.
    unfold option_map. destruct (PTree.get i (snd m)); auto.
  Qed.

End PMap.

(** * An implementation of maps over any type that injects into type [positive] *)

Module Type INDEXED_TYPE.
  Variable t: Set.
  Variable index: t -> positive.
  Hypothesis index_inj: forall (x y: t), index x = index y -> x = y.
  Variable eq: forall (x y: t), {x = y} + {x <> y}.
End INDEXED_TYPE.

Module IMap(X: INDEXED_TYPE).

  Definition elt := X.t.
  Definition elt_eq := X.eq.
  Definition t : Set -> Set := PMap.t.
  Definition eq: forall (A: Set), (forall (x y: A), {x=y} + {x<>y}) ->
                 forall (a b: t A), {a = b} + {a <> b} := PMap.eq.
  Definition init (A: Set) (x: A) := PMap.init x.
  Definition get (A: Set) (i: X.t) (m: t A) := PMap.get (X.index i) m.
  Definition set (A: Set) (i: X.t) (v: A) (m: t A) := PMap.set (X.index i) v m.
  Definition map (A B: Set) (f: A -> B) (m: t A) : t B := PMap.map f m.

  Lemma gi:
    forall (A: Set) (x: A) (i: X.t), get i (init x) = x.
  Proof.
    intros. unfold get, init. apply PMap.gi. 
  Qed.

  Lemma gss:
    forall (A: Set) (i: X.t) (x: A) (m: t A), get i (set i x m) = x.
  Proof.
    intros. unfold get, set. apply PMap.gss.
  Qed.

  Lemma gso:
    forall (A: Set) (i j: X.t) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. unfold get, set. apply PMap.gso. 
    red. intro. apply H. apply X.index_inj; auto. 
  Qed.

  Lemma gsspec:
    forall (A: Set) (i j: X.t) (x: A) (m: t A),
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
    forall (A B: Set) (f: A -> B) (i: X.t) (m: t A),
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
  Variable t: Set.
  Variable eq: forall (x y: t), {x = y} + {x <> y}.
End EQUALITY_TYPE.

Module EMap(X: EQUALITY_TYPE) <: MAP.

  Definition elt := X.t.
  Definition elt_eq := X.eq.
  Definition t (A: Set) := X.t -> A.
  Definition init (A: Set) (v: A) := fun (_: X.t) => v.
  Definition get (A: Set) (x: X.t) (m: t A) := m x.
  Definition set (A: Set) (x: X.t) (v: A) (m: t A) :=
    fun (y: X.t) => if X.eq y x then v else m y.
  Lemma gi:
    forall (A: Set) (i: elt) (x: A), init x i = x.
  Proof.
    intros. reflexivity.
  Qed.
  Lemma gss:
    forall (A: Set) (i: elt) (x: A) (m: t A), (set i x m) i = x.
  Proof.
    intros. unfold set. case (X.eq i i); intro.
    reflexivity. tauto.
  Qed.
  Lemma gso:
    forall (A: Set) (i j: elt) (x: A) (m: t A),
    i <> j -> (set j x m) i = m i.
  Proof.
    intros. unfold set. case (X.eq i j); intro.
    congruence. reflexivity.
  Qed.
  Lemma gsspec:
    forall (A: Set) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Proof.
    intros. unfold get, set, elt_eq. reflexivity.
  Qed.
  Lemma gsident:
    forall (A: Set) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.
  Proof.
    intros. unfold get, set. case (X.eq j i); intro.
    congruence. reflexivity.
  Qed.
  Definition map (A B: Set) (f: A -> B) (m: t A) :=
    fun (x: X.t) => f(m x).
  Lemma gmap:
    forall (A B: Set) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold get, map. reflexivity.
  Qed.
  Lemma exten:
    forall (A: Set) (m1 m2: t A),
    (forall x: X.t, m1 x = m2 x) -> m1 = m2.
  Proof.
    intros. unfold t. apply extensionality. assumption.
  Qed.
End EMap.

(** * Useful notations *)

Notation "a ! b" := (PTree.get b a) (at level 1).
Notation "a !! b" := (PMap.get b a) (at level 1).

(* $Id: Maps.v,v 1.12.4.4 2006/01/07 11:46:55 xleroy Exp $ *)

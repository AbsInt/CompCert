(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*     Xavier Leroy and Damien Doligez, INRIA Paris-Rocquencourt       *)
(*     Andrew W. Appel, Princeton University                           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
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

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Set Implicit Arguments.

(** * The abstract signatures of trees *)

Module Type TREE.
  Parameter elt: Type.
  Parameter elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Parameter t: Type -> Type.
  Parameter empty: forall (A: Type), t A.
  Parameter get: forall (A: Type), elt -> t A -> option A.
  Parameter set: forall (A: Type), elt -> A -> t A -> t A.
  Parameter remove: forall (A: Type), elt -> t A -> t A.

  (** The ``good variables'' properties for trees, expressing
    commutations between [get], [set] and [remove]. *)
  Axiom gempty:
    forall (A: Type) (i: elt), get i (empty A) = None.
  Axiom gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Axiom gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Axiom gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Axiom grs:
    forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Axiom gro:
    forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Axiom grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.

  (** Extensional equality between trees. *)
  Parameter beq: forall (A: Type), (A -> A -> bool) -> t A -> t A -> bool.
  Axiom beq_correct:
    forall (A: Type) (eqA: A -> A -> bool) (t1 t2: t A),
    beq eqA t1 t2 = true <->
    (forall (x: elt),
     match get x t1, get x t2 with
     | None, None => True
     | Some y1, Some y2 => eqA y1 y2 = true
     | _, _ => False
    end).

  (** Applying a function to all data of a tree. *)
  Parameter map:
    forall (A B: Type), (elt -> A -> B) -> t A -> t B.
  Axiom gmap:
    forall (A B: Type) (f: elt -> A -> B) (i: elt) (m: t A),
    get i (map f m) = option_map (f i) (get i m).

  (** Same as [map], but the function does not receive the [elt] argument. *)
  Parameter map1:
    forall (A B: Type), (A -> B) -> t A -> t B.
  Axiom gmap1:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map1 f m) = option_map f (get i m).

  (** Applying a function pairwise to all data of two trees. *)
  Parameter combine:
    forall (A B C: Type), (option A -> option B -> option C) -> t A -> t B -> t C.
  Axiom gcombine:
    forall (A B C: Type) (f: option A -> option B -> option C),
    f None None = None ->
    forall (m1: t A) (m2: t B) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).

  (** Enumerating the bindings of a tree. *)
  Parameter elements:
    forall (A: Type), t A -> list (elt * A).
  Axiom elements_correct:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Axiom elements_complete:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Axiom elements_keys_norepet:
    forall (A: Type) (m: t A),
    list_norepet (List.map (@fst elt A) (elements m)).
  Axiom elements_extensional:
    forall (A: Type) (m n: t A),
    (forall i, get i m = get i n) ->
    elements m = elements n.
  Axiom elements_remove:
    forall (A: Type) i v (m: t A),
    get i m = Some v ->
    exists l1 l2, elements m = l1 ++ (i,v) :: l2 /\ elements (remove i m) = l1 ++ l2.

  (** Folding a function over all bindings of a tree. *)
  Parameter fold:
    forall (A B: Type), (B -> elt -> A -> B) -> t A -> B -> B.
  Axiom fold_spec:
    forall (A B: Type) (f: B -> elt -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  (** Same as [fold], but the function does not receive the [elt] argument. *)
  Parameter fold1:
    forall (A B: Type), (B -> A -> B) -> t A -> B -> B.
  Axiom fold1_spec:
    forall (A B: Type) (f: B -> A -> B) (v: B) (m: t A),
    fold1 f m v =
    List.fold_left (fun a p => f a (snd p)) (elements m) v.
End TREE.

(** * The abstract signatures of maps *)

Module Type MAP.
  Parameter elt: Type.
  Parameter elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Parameter t: Type -> Type.
  Parameter init: forall (A: Type), A -> t A.
  Parameter get: forall (A: Type), elt -> t A -> A.
  Parameter set: forall (A: Type), elt -> A -> t A -> t A.
  Axiom gi:
    forall (A: Type) (i: elt) (x: A), get i (init x) = x.
  Axiom gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = x.
  Axiom gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Axiom gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Axiom gsident:
    forall (A: Type) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.
  Parameter map: forall (A B: Type), (A -> B) -> t A -> t B.
  Axiom gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
End MAP.

(** * An implementation of trees over type [positive] *)

Module PTree <: TREE.
  Definition elt := positive.
  Definition elt_eq := peq.

(** ** Representation of trees *)

(** The type [tree'] of nonempty trees.  Each constructor is of the form
    [NodeXYZ], where the bit [X] says whether there is a left subtree,
    [Y] whether there is a value at this node, and [Z] whether there is
    a right subtree. *)

  Inductive tree' (A: Type) : Type := 
  | Node001: tree' A -> tree' A
  | Node010: A -> tree' A
  | Node011: A -> tree' A -> tree' A
  | Node100: tree' A -> tree' A
  | Node101: tree' A -> tree' A ->tree' A
  | Node110: tree' A -> A -> tree' A
  | Node111: tree' A -> A -> tree' A -> tree' A.

  Inductive tree (A: Type) : Type := 
  | Empty : tree A
  | Nodes: tree' A -> tree A.

  Arguments Node001 {A} _.
  Arguments Node010 {A} _.
  Arguments Node011 {A} _ _.
  Arguments Node100 {A} _.
  Arguments Node101 {A} _ _.
  Arguments Node110 {A} _ _.
  Arguments Node111 {A} _ _ _.

  Arguments Empty {A}.
  Arguments Nodes {A} _.

  Scheme tree'_ind := Induction for tree' Sort Prop.

  Definition t := tree.

  (** A smart constructor for type [tree]: given a (possibly empty)
      left subtree, a (possibly absent) value, and a (possibly empty)
      right subtree, it builds the corresponding tree. *)

  Definition Node {A} (l: tree A) (o: option A) (r: tree A) : tree A := 
    match l,o,r with
    | Empty, None, Empty => Empty
    | Empty, None, Nodes r' => Nodes (Node001 r')
    | Empty, Some x, Empty => Nodes (Node010 x)
    | Empty, Some x, Nodes r' => Nodes (Node011 x r')
    | Nodes l', None, Empty => Nodes (Node100 l')
    | Nodes l', None, Nodes r' => Nodes (Node101 l' r')
    | Nodes l', Some x, Empty => Nodes (Node110 l' x)
    | Nodes l', Some x, Nodes r' => Nodes (Node111 l' x r')
    end.

(** ** Basic operations: [empty], [get], [set], [remove] *)

  Definition empty (A: Type) : t A := Empty.

  Fixpoint get' {A} (p: positive) (m: tree' A) : option A :=
    match p, m with
    | xH, Node001 _ => None
    | xH, Node010 x => Some x
    | xH, Node011 x _ => Some x
    | xH, Node100 _ => None
    | xH, Node101 _ _ => None
    | xH, Node110 _ x => Some x
    | xH, Node111 _ x _ => Some x
    | xO q, Node001 _ => None
    | xO q, Node010 _ => None
    | xO q, Node011 _ _ => None
    | xO q, Node100 m' => get' q m'
    | xO q, Node101 m' _ => get' q m'
    | xO q, Node110 m' _ => get' q m'
    | xO q, Node111 m' _ _ => get' q m'
    | xI q, Node001 m' => get' q m'
    | xI q, Node010 _ => None
    | xI q, Node011 _ m' => get' q m'
    | xI q, Node100 m' => None
    | xI q, Node101 _ m' => get' q m'
    | xI q, Node110 _ _ => None
    | xI q, Node111 _ _ m' => get' q m'
    end.

  Definition get {A} (p: positive) (m: tree A) : option A :=
    match m with
    | Empty => None
    | Nodes m' => get' p m'
    end.

  (** [set0 p x] constructs the singleton tree that maps [p] to [x]
      and has no other bindings. *)

  Fixpoint set0 {A} (p: positive) (x: A) : tree' A :=
  match p with
  | xH => Node010 x
  | xO q => Node100 (set0 q x)
  | xI q => Node001 (set0 q x)
  end.

  Fixpoint set' {A} (p: positive) (x: A) (m: tree' A) : tree' A :=
  match p, m with
  | xH, Node001 r => Node011 x r
  | xH, Node010 _ => Node010 x
  | xH, Node011 _ r => Node011 x r
  | xH, Node100 l => Node110 l x
  | xH, Node101 l r => Node111 l x r
  | xH, Node110 l _ => Node110 l x
  | xH, Node111 l _ r => Node111 l x r
  | xO q, Node001 r => Node101 (set0 q x) r
  | xO q, Node010 y => Node110 (set0 q x) y
  | xO q, Node011 y r => Node111 (set0 q x) y r
  | xO q, Node100 l => Node100 (set' q x l)
  | xO q, Node101 l r => Node101 (set' q x l) r
  | xO q, Node110 l y => Node110 (set' q x l) y
  | xO q, Node111 l y r => Node111 (set' q x l) y r
  | xI q, Node001 r => Node001 (set' q x r)
  | xI q, Node010 y => Node011 y (set0 q x)
  | xI q, Node011 y r => Node011 y (set' q x r)
  | xI q, Node100 l => Node101 l (set0 q x)
  | xI q, Node101 l r => Node101 l (set' q x r)
  | xI q, Node110 l y => Node111 l y (set0 q x)
  | xI q, Node111 l y r => Node111 l y (set' q x r)
  end.

  Definition set {A} (p: positive) (x: A) (m: tree A) : tree A :=
  match m with
  | Empty => Nodes (set0 p x)
  | Nodes m' => Nodes (set' p x m')
  end.

  (** Removal in a nonempty tree produces a possibly empty tree.
      To simplify the code, we use the [Node] smart constructor in the
      cases where the result can be empty or nonempty, depending on the
      results of the recursive calls. *)

  Fixpoint rem' {A} (p: positive) (m: tree' A) : tree A :=
  match p, m with
  | xH, Node001 r => Nodes m
  | xH, Node010 _ => Empty
  | xH, Node011 _ r => Nodes (Node001 r)
  | xH, Node100 l => Nodes m
  | xH, Node101 l r => Nodes m
  | xH, Node110 l _ => Nodes (Node100 l)
  | xH, Node111 l _ r => Nodes (Node101 l r)
  | xO q, Node001 r => Nodes m
  | xO q, Node010 y => Nodes m
  | xO q, Node011 y r => Nodes m
  | xO q, Node100 l => Node (rem' q l) None Empty
  | xO q, Node101 l r => Node (rem' q l) None (Nodes r)
  | xO q, Node110 l y => Node (rem' q l) (Some y) Empty
  | xO q, Node111 l y r => Node (rem' q l) (Some y) (Nodes r)
  | xI q, Node001 r => Node Empty None (rem' q r)
  | xI q, Node010 y => Nodes m
  | xI q, Node011 y r => Node Empty (Some y) (rem' q r)
  | xI q, Node100 l => Nodes m
  | xI q, Node101 l r => Node (Nodes l) None (rem' q r)
  | xI q, Node110 l y => Nodes m
  | xI q, Node111 l y r => Node (Nodes l) (Some y) (rem' q r)
  end.

  (** This use of [Node] causes some run-time overhead, which we eliminate
      by partial evaluation within Coq. *)

  Definition remove' := Eval cbv [rem' Node] in @rem'.

  Definition remove {A} (p: positive) (m: tree A) : tree A :=
  match m with
  | Empty => Empty
  | Nodes m' => remove' p m'
  end.

(** ** Good variable properties for the basic operations *)

  Theorem gempty:
    forall (A: Type) (i: positive), get i (empty A) = None.
  Proof. reflexivity. Qed.

  Lemma gEmpty:
    forall (A: Type) (i: positive), get i (@Empty A) = None.
  Proof. reflexivity. Qed.

  Lemma gss0: forall {A} p (x: A), get' p (set0 p x) = Some x.
  Proof. induction p; simpl; auto. Qed.

  Lemma gso0: forall {A} p q (x: A), p<>q -> get' p (set0 q x) = None.
  Proof.
    induction p; destruct q; simpl; intros; auto; try apply IHp; congruence.
  Qed.

  Theorem gss:
    forall (A: Type) (i: positive) (x: A) (m: tree A), get i (set i x m) = Some x.
  Proof.
   intros. destruct m as [|m]; simpl.
   - apply gss0.
   - revert m; induction i; destruct m; simpl; intros; auto using gss0.
  Qed.

  Theorem gso:
    forall (A: Type) (i j: positive) (x: A) (m: tree A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
   intros. destruct m as [|m]; simpl.
   - apply gso0; auto.
   - revert m j H; induction i; destruct j,m; simpl; intros; auto;
     solve [apply IHi; congruence | apply gso0; congruence | congruence].
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    get i (set j x m) = if peq i j then Some x else get i m.
  Proof.
    intros.
    destruct (peq i j); [ rewrite e; apply gss | apply gso; auto ].
  Qed.

  Lemma gNode:
    forall {A} (i: positive) (l: tree A) (x: option A) (r: tree A),
    get i (Node l x r) = match i with xH => x | xO j => get j l | xI j => get j r end.
  Proof.
    intros. destruct l, x, r; simpl; auto; destruct i; auto.
  Qed.

  Theorem grs:
    forall (A: Type) (i: positive) (m: tree A), get i (remove i m) = None.
  Proof.
    Local Opaque Node.
    destruct m as [ |m]; simpl. auto.
    change (remove' i m) with (rem' i m).
    revert m. induction i; destruct m; simpl; auto; rewrite gNode; auto.
  Qed.

  Theorem gro:
    forall (A: Type) (i j: positive) (m: tree A),
    i <> j -> get i (remove j m) = get i m.
  Proof.
    Local Opaque Node.
    destruct m as [ |m]; simpl. auto.
    change (remove' j m) with (rem' j m).
    revert j m. induction i; destruct j, m; simpl; intros; auto;
    solve [ congruence
          | rewrite gNode; auto; apply IHi; congruence ].
  Qed.

  Theorem grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof.
    intros. destruct (elt_eq i j). subst j. apply grs. apply gro; auto.
  Qed.

(** ** Custom case analysis principles and induction principles *)

(** We can view trees as being of one of two (non-exclusive)
    cases: either [Empty] for an empty tree, or [Node l o r] for a
    nonempty tree, with [l] and [r] the left and right subtrees
    and [o] an optional value.  The [Empty] constructor and the [Node]
    smart function defined above provide one half of the view: the one
    that lets us construct values of type [tree A].

    We now define the other half of the view: the one that lets us
    inspect and recurse over values of type [tree A].  This is achieved
    by defining appropriate principles for case analysis and induction. *)

  Definition not_trivially_empty {A} (l: tree A) (o: option A) (r: tree A) :=
    match l, o, r with
    | Empty, None, Empty => False
    | _, _, _ => True
    end.

  (** A case analysis principle *)

  Section TREE_CASE.

  Context {A B: Type}
          (empty: B)
          (node: tree A -> option A -> tree A -> B).

  Definition tree_case (m: tree A) : B :=
    match m with
    | Empty => empty
    | Nodes (Node001 r) => node Empty None (Nodes r)
    | Nodes (Node010 x) => node Empty (Some x) Empty
    | Nodes (Node011 x r) => node Empty (Some x) (Nodes r)
    | Nodes (Node100 l) => node (Nodes l) None Empty
    | Nodes (Node101 l r) => node (Nodes l) None (Nodes r)
    | Nodes (Node110 l x) => node (Nodes l) (Some x) Empty
    | Nodes (Node111 l x r) => node (Nodes l) (Some x) (Nodes r)
    end.

  Lemma unroll_tree_case: forall l o r,
    not_trivially_empty l o r ->
    tree_case (Node l o r) = node l o r.
  Proof.
    destruct l, o, r; simpl; intros; auto. contradiction.
  Qed.

  End TREE_CASE.

  (** A recursion principle *)

  Section TREE_REC.

  Context {A B: Type}
          (empty: B)
          (node: tree A -> B -> option A -> tree A -> B -> B).

  Fixpoint tree_rec' (m: tree' A) : B :=
    match m with
    | Node001 r => node Empty empty None (Nodes r) (tree_rec' r)
    | Node010 x => node Empty empty (Some x) Empty empty
    | Node011 x r => node Empty empty (Some x) (Nodes r) (tree_rec' r)
    | Node100 l => node (Nodes l) (tree_rec' l) None Empty empty
    | Node101 l r => node (Nodes l) (tree_rec' l) None (Nodes r) (tree_rec' r)
    | Node110 l x => node (Nodes l) (tree_rec' l) (Some x) Empty empty
    | Node111 l x r => node (Nodes l) (tree_rec' l) (Some x) (Nodes r) (tree_rec' r)
    end.

  Definition tree_rec (m: tree A) : B :=
    match m with
    | Empty => empty
    | Nodes m' => tree_rec' m'
    end.

  Lemma unroll_tree_rec: forall l o r,
    not_trivially_empty l o r ->
    tree_rec (Node l o r) = node l (tree_rec l) o r (tree_rec r).
  Proof.
    destruct l, o, r; simpl; intros; auto. contradiction.
  Qed.

  End TREE_REC.

  (** A double recursion principle *)

  Section TREE_REC2.

  Context {A B C: Type}
          (base: C)
          (base1: tree B -> C) 
          (base2: tree A -> C)
          (nodes: forall (l1: tree A) (o1: option A) (r1: tree A)
                         (l2: tree B) (o2: option B) (r2: tree B)
                         (lrec: C) (rrec: C), C).

  Fixpoint tree_rec2' (m1: tree' A) (m2: tree' B) : C.
  Proof.
    destruct m1 as [ r1 | x1 | x1 r1 | l1 | l1 r1 | l1 x1 | l1 x1 r1 ];
    destruct m2 as [ r2 | x2 | x2 r2 | l2 | l2 r2 | l2 x2 | l2 x2 r2 ];
    (apply nodes;
    [ solve [ exact (Nodes l1) | exact Empty ]
    | solve [ exact (Some x1)  | exact None ]
    | solve [ exact (Nodes r1) | exact Empty ]
    | solve [ exact (Nodes l2) | exact Empty ]
    | solve [ exact (Some x2)  | exact None ]
    | solve [ exact (Nodes r2) | exact Empty ]
    | solve [ exact (tree_rec2' l1 l2) | exact (base2 (Nodes l1)) | exact (base1 (Nodes l2)) | exact base ]
    | solve [ exact (tree_rec2' r1 r2) | exact (base2 (Nodes r1)) | exact (base1 (Nodes r2)) | exact base ]
    ]).
  Defined.

  Definition tree_rec2 (a: tree A) (b: tree B) : C :=
    match a, b with
    | Empty, Empty => base
    | Empty, _ => base1 b
    | _, Empty => base2 a
    | Nodes a', Nodes b' => tree_rec2' a' b'
    end.

  Lemma unroll_tree_rec2_NE:
    forall l1 o1 r1,
    not_trivially_empty l1 o1 r1 ->
    tree_rec2 (Node l1 o1 r1) Empty = base2 (Node l1 o1 r1).
  Proof.
    intros. destruct l1, o1, r1; try contradiction; reflexivity.
  Qed.

  Lemma unroll_tree_rec2_EN:
    forall l2 o2 r2,
    not_trivially_empty l2 o2 r2 ->
    tree_rec2 Empty (Node l2 o2 r2) = base1 (Node l2 o2 r2).
  Proof.
    intros. destruct l2, o2, r2; try contradiction; reflexivity.
  Qed.

  Lemma unroll_tree_rec2_NN:
    forall l1 o1 r1 l2 o2 r2,
    not_trivially_empty l1 o1 r1 -> not_trivially_empty l2 o2 r2 ->
    tree_rec2 (Node l1 o1 r1) (Node l2 o2 r2) =
    nodes l1 o1 r1 l2 o2 r2 (tree_rec2 l1 l2) (tree_rec2 r1 r2).
  Proof.
    intros.
    destruct l1, o1, r1; try contradiction; destruct l2, o2, r2; try contradiction; reflexivity.
  Qed.

  End TREE_REC2.

(** An induction principle *)

  Section TREE_IND.

  Context {A: Type} (P: tree A -> Type)
          (empty: P Empty)
          (node: forall l, P l -> forall o r, P r -> not_trivially_empty l o r ->
                 P (Node l o r)).

  Program Fixpoint tree_ind' (m: tree' A) : P (Nodes m) :=
    match m with
    | Node001 r => @node Empty empty None (Nodes r) (tree_ind' r) _
    | Node010 x => @node Empty empty (Some x) Empty empty _
    | Node011 x r => @node Empty empty (Some x) (Nodes r) (tree_ind' r) _
    | Node100 l => @node (Nodes l) (tree_ind' l) None Empty empty _
    | Node101 l r => @node (Nodes l) (tree_ind' l) None (Nodes r) (tree_ind' r) _
    | Node110 l x => @node (Nodes l) (tree_ind' l) (Some x) Empty empty _
    | Node111 l x r => @node (Nodes l) (tree_ind' l) (Some x) (Nodes r) (tree_ind' r) _
    end.

  Definition tree_ind (m: tree A) : P m :=
    match m with
    | Empty => empty
    | Nodes m' => tree_ind' m'
    end.

  End TREE_IND.

(** ** Extensionality property *)

  Lemma tree'_not_empty:
    forall {A} (m: tree' A), exists i, get' i m <> None.
  Proof.
   induction m; simpl; try destruct IHm as [p H].
   - exists (xI p); auto.
   - exists xH; simpl; congruence.
   - exists xH; simpl; congruence.
   - exists (xO p); auto.
   - destruct IHm1 as [p H]; exists (xO p); auto.
   - exists xH; simpl; congruence.
   - exists xH; simpl; congruence.
  Qed.

  Corollary extensionality_empty:
    forall {A} (m: tree A),
    (forall i, get i m = None) -> m = Empty.
  Proof.
    intros. destruct m as [ | m]; auto. destruct (tree'_not_empty m) as [i GET].
    elim GET. apply H.
  Qed.

  Theorem extensionality:
    forall (A: Type) (m1 m2: tree A),
    (forall i, get i m1 = get i m2) -> m1 = m2.
  Proof.
    intros A. induction m1 using tree_ind; induction m2 using tree_ind; intros.
  - auto.
  - symmetry. apply extensionality_empty. intros; symmetry; apply H0.
  - apply extensionality_empty. apply H0.
  - f_equal.
    + apply IHm1_1. intros. specialize (H1 (xO i)); rewrite ! gNode in H1. auto.
    + specialize (H1 xH); rewrite ! gNode in H1. auto.
    + apply IHm1_2. intros. specialize (H1 (xI i)); rewrite ! gNode in H1. auto.
  Qed.

  (** Some consequences of extensionality *)

  Theorem gsident:
    forall {A} (i: positive) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.
  Proof.
    intros; apply extensionality; intros j.
    rewrite gsspec. destruct (peq j i); congruence.
  Qed.

  Theorem set2:
    forall {A} (i: elt) (m: t A) (v1 v2: A),
    set i v2 (set i v1 m) = set i v2 m.
  Proof.
    intros; apply extensionality; intros j.
    rewrite ! gsspec. destruct (peq j i); auto.
  Qed.

(** ** Boolean equality *)

  Section BOOLEAN_EQUALITY.

    Variable A: Type.
    Variable beqA: A -> A -> bool.

    Fixpoint beq' (m1 m2: tree' A) {struct m1} : bool :=
    match m1, m2 with
    | Node001 r1, Node001 r2 => beq' r1 r2
    | Node010 x1, Node010 x2 => beqA x1 x2
    | Node011 x1 r1, Node011 x2 r2 => beqA x1 x2 && beq' r1 r2
    | Node100 l1, Node100 l2 => beq' l1 l2
    | Node101 l1 r1, Node101 l2 r2 => beq' l1 l2 && beq' r1 r2
    | Node110 l1 x1, Node110 l2 x2 => beqA x1 x2 && beq' l1 l2
    | Node111 l1 x1 r1, Node111 l2 x2 r2  => beqA x1 x2 && beq' l1 l2 && beq' r1 r2
    | _, _ => false
    end.

    Definition beq (m1 m2: t A) : bool :=
    match m1, m2 with
    | Empty, Empty => true
    | Nodes m1', Nodes m2' => beq' m1' m2'
    | _, _ => false
    end.

    Let beq_optA (o1 o2: option A) : bool :=
      match o1, o2 with
      | None, None => true
      | Some a1, Some a2 => beqA a1 a2
      | _, _ => false
      end.

    Lemma beq_correct_bool:
      forall m1 m2,
      beq m1 m2 = true <-> (forall x, beq_optA (get x m1) (get x m2) = true).
    Proof.
      Local Transparent Node.
      assert (beq_NN: forall l1 o1 r1 l2 o2 r2,
              not_trivially_empty l1 o1 r1 ->
              not_trivially_empty l2 o2 r2 ->
              beq (Node l1 o1 r1) (Node l2 o2 r2) =
              beq l1 l2 && beq_optA o1 o2 && beq r1 r2).
      { intros.
        destruct l1, o1, r1; try contradiction; destruct l2, o2, r2; try contradiction;
        simpl; rewrite ? andb_true_r, ? andb_false_r; auto.
        rewrite andb_comm; auto.
        f_equal; rewrite andb_comm; auto. }
      induction m1 using tree_ind; [|induction m2 using tree_ind].
    - intros. simpl; split; intros.
      + destruct m2; try discriminate. simpl; auto.
      + replace m2 with (@Empty A); auto. apply extensionality; intros x.
        specialize (H x). destruct (get x m2); simpl; congruence.
    - split; intros.
      + destruct (Node l o r); try discriminate. simpl; auto.
      + replace (Node l o r) with (@Empty A); auto. apply extensionality; intros x.
        specialize (H0 x). destruct (get x (Node l o r)); simpl in *; congruence.
    - rewrite beq_NN by auto. split; intros.
      + InvBooleans. rewrite ! gNode. destruct x.
        * apply IHm0; auto.
        * apply IHm1; auto.
        * auto.
      + apply andb_true_intro; split; [apply andb_true_intro; split|].
        * apply IHm1. intros. specialize (H1 (xO x)); rewrite ! gNode in H1; auto.
        * specialize (H1 xH); rewrite ! gNode in H1; auto.
        * apply IHm0. intros. specialize (H1 (xI x)); rewrite ! gNode in H1; auto.
    Qed.

    Theorem beq_correct:
      forall m1 m2,
      beq m1 m2 = true <->
      (forall (x: elt),
       match get x m1, get x m2 with
       | None, None => True
       | Some y1, Some y2 => beqA y1 y2 = true
       | _, _ => False
       end).
    Proof.
      intros. rewrite beq_correct_bool. unfold beq_optA. split; intros.
    - specialize (H x). destruct (get x m1), (get x m2); intuition congruence.
    - specialize (H x). destruct (get x m1), (get x m2); intuition auto.
    Qed.

  End BOOLEAN_EQUALITY.

(** ** Collective operations *)

  Fixpoint prev_append (i j: positive) {struct i} : positive :=
    match i with
      | xH => j
      | xI i' => prev_append i' (xI j)
      | xO i' => prev_append i' (xO j)
    end.

  Definition prev (i: positive) : positive :=
    prev_append i xH.

  Lemma prev_append_prev i j:
    prev (prev_append i j) = prev_append j i.
  Proof.
    revert j. unfold prev.
    induction i as [i IH|i IH|]. 3: reflexivity.
    intros j. simpl. rewrite IH. reflexivity.
    intros j. simpl. rewrite IH. reflexivity.
  Qed.

  Lemma prev_involutive i :
    prev (prev i) = i.
  Proof (prev_append_prev i xH).

  Lemma prev_append_inj i j j' :
    prev_append i j = prev_append i j' -> j = j'.
  Proof.
    revert j j'.
    induction i as [i Hi|i Hi|]; intros j j' H; auto;
    specialize (Hi _ _ H); congruence.
  Qed.

  Fixpoint map' {A B} (f: positive -> A -> B) (m: tree' A) (i: positive)
           {struct m} : tree' B :=
    match m with
    | Node001 r => Node001 (map' f r (xI i))
    | Node010 x => Node010 (f (prev i) x)
    | Node011 x r => Node011 (f (prev i) x) (map' f r (xI i))
    | Node100 l => Node100 (map' f l (xO i))
    | Node101 l r => Node101 (map' f l (xO i)) (map' f r (xI i))
    | Node110 l x => Node110 (map' f l (xO i)) (f (prev i) x)
    | Node111 l x r => Node111 (map' f l (xO i)) (f (prev i) x) (map' f r (xI i))
    end.

  Definition map {A B} (f: positive -> A -> B) (m: tree A) :=
    match m with
    | Empty => Empty
    | Nodes m => Nodes (map' f m xH)
    end.

  Lemma gmap':
    forall {A B} (f: positive -> A -> B) (i j : positive) (m: tree' A),
    get' i (map' f m j) = option_map (f (prev (prev_append i j))) (get' i m).
  Proof.
    induction i; intros; destruct m; simpl; auto.
  Qed.

  Theorem gmap:
    forall {A B} (f: positive -> A -> B) (i: positive) (m: t A),
    get i (map f m) = option_map (f i) (get i m).
  Proof.
    intros; destruct m as [|m]; simpl. auto. rewrite gmap'. repeat f_equal. exact (prev_involutive i).
  Qed.

  Fixpoint map1' {A B} (f: A -> B) (m: tree' A) {struct m} : tree' B :=
    match m with
    | Node001 r => Node001 (map1' f r)
    | Node010 x => Node010 (f x)
    | Node011 x r => Node011 (f x) (map1' f r)
    | Node100 l => Node100 (map1' f l)
    | Node101 l r => Node101 (map1' f l) (map1' f r)
    | Node110 l x => Node110 (map1' f l) (f x)
    | Node111 l x r => Node111 (map1' f l) (f x) (map1' f r)
    end.

  Definition map1 {A B} (f: A -> B) (m: t A) : t B :=
    match m with
    | Empty => Empty
    | Nodes m => Nodes (map1' f m)
    end.

  Theorem gmap1:
    forall {A B} (f: A -> B) (i: elt) (m: t A),
    get i (map1 f m) = option_map f (get i m).
  Proof.
    intros. destruct m as [|m]; simpl. auto.
    revert i; induction m; destruct i; simpl; auto.
  Qed.

  Definition map_filter1_nonopt {A B} (f: A -> option B) (m: tree A) : tree B :=
    tree_rec
      Empty
      (fun l lrec o r rrec => Node lrec (match o with None => None | Some a => f a end) rrec)
      m.

  Local Transparent Node.

  Definition map_filter1 :=
    Eval cbv [map_filter1_nonopt tree_rec tree_rec' Node] in @map_filter1_nonopt.

  Lemma gmap_filter1:
    forall {A B} (f: A -> option B) (m: tree A) (i: positive),
    get i (map_filter1 f m) = match get i m with None => None | Some a => f a end.
  Proof.
    change @map_filter1 with @map_filter1_nonopt. unfold map_filter1_nonopt.
    intros until f. induction m using tree_ind; intros.
  - auto.
  - rewrite unroll_tree_rec by auto. rewrite ! gNode; destruct i; auto.
  Qed.

  Definition filter1 {A} (pred: A -> bool) (m: t A) : t A :=
    map_filter1 (fun a => if pred a then Some a else None) m.

  Theorem gfilter1:
    forall {A} (pred: A -> bool) (i: elt) (m: t A),
    get i (filter1 pred m) =
    match get i m with None => None | Some x => if pred x then Some x else None end.
  Proof.
    intros. apply gmap_filter1.
  Qed. 

  Section COMBINE.

  Variables A B C: Type.
  Variable f: option A -> option B -> option C.
  Hypothesis f_none_none: f None None = None.

  Let combine_l := map_filter1 (fun a => f (Some a) None).
  Let combine_r := map_filter1 (fun b => f None (Some b)).

  Let combine_nonopt (m1: tree A) (m2: tree B) : tree C :=
    tree_rec2
      Empty
      combine_r
      combine_l
      (fun l1 o1 r1 l2 o2 r2 lrec rrec =>
        Node lrec
             (match o1, o2 with None, None => None | _, _ => f o1 o2 end)
             rrec)
      m1 m2.

  Definition combine :=
    Eval cbv [combine_nonopt tree_rec2 tree_rec2'] in combine_nonopt.

  Lemma gcombine_l: forall m i, get i (combine_l m) = f (get i m) None.
  Proof.
    intros; unfold combine_l; rewrite gmap_filter1. destruct (get i m); auto.
  Qed.

  Lemma gcombine_r: forall m i, get i (combine_r m) = f None (get i m).
  Proof.
    intros; unfold combine_r; rewrite gmap_filter1. destruct (get i m); auto.
  Qed.

  Theorem gcombine:
      forall (m1: t A) (m2: t B) (i: positive),
      get i (combine m1 m2) = f (get i m1) (get i m2).
  Proof.
    change combine with combine_nonopt.
    induction m1 using tree_ind; induction m2 using tree_ind; intros.
  - auto.
  - unfold combine_nonopt; rewrite unroll_tree_rec2_EN by auto. apply gcombine_r.
  - unfold combine_nonopt; rewrite unroll_tree_rec2_NE by auto. apply gcombine_l.
  - unfold combine_nonopt; rewrite unroll_tree_rec2_NN by auto.
    rewrite ! gNode; destruct i; auto. destruct o, o0; auto.
  Qed.

  End COMBINE.

  Theorem combine_commut:
    forall (A B: Type) (f g: option A -> option A -> option B),
    f None None = None -> g None None = None ->
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.
  Proof.
    intros. apply extensionality; intros i. rewrite ! gcombine by auto. auto.
  Qed.

(** ** List of all bindings *)

  Fixpoint xelements' {A} (m : tree' A) (i: positive) (k: list (positive * A))
                     {struct m} : list (positive * A) :=
    match m with
    | Node001 r => xelements' r (xI i) k
    | Node010 x => (prev i, x) :: k
    | Node011 x r => (prev i, x) :: xelements' r (xI i) k
    | Node100 l => xelements' l (xO i) k
    | Node101 l r => xelements' l (xO i) (xelements' r (xI i) k)
    | Node110 l x => xelements' l (xO i) ((prev i, x)::k)
    | Node111 l x r => xelements' l (xO i) ((prev i, x):: (xelements' r (xI i) k))
    end.

  Definition elements {A} (m : t A) : list (positive * A) := 
    match m with Empty => nil | Nodes m' => xelements' m' xH nil end.

  Definition xelements {A} (m : t A) (i: positive) : list (positive * A) := 
    match m with Empty => nil | Nodes m' => xelements' m' i nil end.

  Lemma xelements'_append:
    forall A (m: tree' A) i k1 k2,
    xelements' m i (k1 ++ k2) = xelements' m i k1 ++ k2.
  Proof.
    induction m; intros; simpl; auto.
  - f_equal; auto.
  - rewrite IHm2, IHm1. auto.
  - rewrite <- IHm. auto.
  - rewrite IHm2, <- IHm1. auto.
  Qed.

  Lemma xelements_Node:
    forall A (l: tree A) (o: option A) (r: tree A) i,
    xelements (Node l o r) i =
       xelements l (xO i)
    ++ match o with None => nil | Some v => (prev i, v) :: nil end
    ++ xelements r (xI i).
  Proof.
    Local Transparent Node.
    intros; destruct l, o, r; simpl; rewrite <- ? xelements'_append; auto.
  Qed.

  Lemma xelements_correct:
    forall A (m: tree A) i j v,
    get i m = Some v -> In (prev (prev_append i j), v) (xelements m j).
  Proof.
    intros A. induction m using tree_ind; intros.
  - discriminate.
  - rewrite xelements_Node, ! in_app. rewrite gNode in H0. destruct i.
    + right; right. apply (IHm2 i (xI j)); auto.
    + left. apply (IHm1 i (xO j)); auto.
    + right; left. subst o. rewrite prev_append_prev. auto with coqlib.
  Qed.

  Theorem elements_correct:
    forall A (m: t A) (i: positive) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Proof.
    intros A m i v H.
    generalize (xelements_correct m i xH H). rewrite prev_append_prev. auto.
  Qed.

  Lemma in_xelements:
    forall A (m: tree A) (i k: positive) (v: A) ,
    In (k, v) (xelements m i) ->
    exists j, k = prev (prev_append j i) /\ get j m = Some v.
  Proof.
    intros A. induction m using tree_ind; intros.
  - elim H.
  - rewrite xelements_Node, ! in_app in H0. destruct H0 as [P | [P | P]].
    + exploit IHm1; eauto. intros (j & Q & R). exists (xO j); rewrite gNode; auto.
    + destruct o; simpl in P; intuition auto. inv H0. exists xH; rewrite gNode; auto.
    + exploit IHm2; eauto. intros (j & Q & R). exists (xI j); rewrite gNode; auto.
  Qed.

  Theorem elements_complete:
    forall A (m: t A) (i: positive) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Proof.
    intros A m i v H. exploit in_xelements; eauto. intros (j & P & Q).
    rewrite prev_append_prev in P. change i with (prev_append 1 i) in P.
    exploit prev_append_inj; eauto. intros; congruence.
  Qed.

  Definition xkeys {A} (m: t A) (i: positive) := List.map fst (xelements m i).

  Lemma xkeys_Node:
    forall A (m1: t A) o (m2: t A) i,
    xkeys (Node m1 o m2) i =
       xkeys m1 (xO i)
    ++ match o with None => nil | Some v => prev i :: nil end
    ++ xkeys m2 (xI i).
  Proof.
    intros. unfold xkeys. rewrite xelements_Node, ! map_app. destruct o; auto.
  Qed.

  Lemma in_xkeys:
    forall (A: Type) (m: t A) (i k: positive),
    In k (xkeys m i) ->
    (exists j, k = prev (prev_append j i)).
  Proof.
    unfold xkeys; intros.
    apply (list_in_map_inv) in H. destruct H as ((j, v) & -> & H).
    exploit in_xelements; eauto. intros (k & P & Q). exists k; auto.
  Qed.

  Lemma xelements_keys_norepet:
    forall (A: Type) (m: t A) (i: positive),
    list_norepet (xkeys m i).
  Proof.
    intros A; induction m using tree_ind; intros.
  - constructor.
  - assert (NOTIN1: ~ In (prev i) (xkeys l (xO i))).
    { red; intros. exploit in_xkeys; eauto. intros (j & EQ).
      rewrite prev_append_prev in EQ. simpl in EQ. apply prev_append_inj in EQ. discriminate. }
    assert (NOTIN2: ~ In (prev i) (xkeys r (xI i))).
    { red; intros. exploit in_xkeys; eauto. intros (j & EQ).
      rewrite prev_append_prev in EQ. simpl in EQ. apply prev_append_inj in EQ. discriminate. }
    assert (DISJ: forall x, In x (xkeys l (xO i)) -> In x (xkeys r (xI i)) -> False).
    { intros. exploit in_xkeys. eexact H0. intros (j1 & EQ1).
      exploit in_xkeys. eexact H1. intros (j2 & EQ2).
      rewrite prev_append_prev in *. simpl in *. rewrite EQ2 in EQ1. apply prev_append_inj in EQ1. discriminate. }
    rewrite xkeys_Node. apply list_norepet_append. auto.
    destruct o; simpl; auto. constructor; auto.
    red; intros. red; intros; subst y. destruct o; simpl in H1.
    destruct H1. subst x. tauto. eauto. eauto.
  Qed.

  Theorem elements_keys_norepet:
    forall A (m: t A),
    list_norepet (List.map (@fst elt A) (elements m)).
  Proof.
    intros. apply (xelements_keys_norepet m xH).
  Qed.

  Remark xelements_empty:
    forall A (m: t A) i, (forall i, get i m = None) -> xelements m i = nil.
  Proof.
    intros. replace m with (@Empty A). auto.
    apply extensionality; intros. symmetry; auto.
  Qed.

  Theorem elements_canonical_order':
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
    (forall i, option_rel R (get i m) (get i n)) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (elements m) (elements n).
  Proof.
    intros until n.
    change (elements m) with (xelements m xH). change (elements n) with (xelements n xH).
    generalize 1%positive. revert m n.
    induction m using tree_ind; [ | induction n using tree_ind]; intros until p; intros REL.
  - replace n with (@Empty B). constructor.
    apply extensionality; intros. specialize (REL i). simpl in *. inv REL; auto.
  - replace (Node l o r) with (@Empty A). constructor.
    apply extensionality; intros. specialize (REL i). simpl in *. inv REL; auto.
  - rewrite ! xelements_Node. repeat apply list_forall2_app.
    + apply IHm. intros. specialize (REL (xO i)). rewrite ! gNode in REL; auto.
    + specialize (REL xH). rewrite ! gNode in REL. inv REL; constructor; auto using list_forall2_nil.
    + apply IHm0. intros. specialize (REL (xI i)). rewrite ! gNode in REL; auto.
  Qed.

  Theorem elements_canonical_order:
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
    (forall i x, get i m = Some x -> exists y, get i n = Some y /\ R x y) ->
    (forall i y, get i n = Some y -> exists x, get i m = Some x /\ R x y) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (elements m) (elements n).
  Proof.
    intros. apply elements_canonical_order'.
    intros. destruct (get i m) as [x|] eqn:GM.
    exploit H; eauto. intros (y & P & Q). rewrite P; constructor; auto.
    destruct (get i n) as [y|] eqn:GN.
    exploit H0; eauto. intros (x & P & Q). congruence.
    constructor.
  Qed.

  Theorem elements_extensional:
    forall (A: Type) (m n: t A),
    (forall i, get i m = get i n) ->
    elements m = elements n.
  Proof.
    intros. replace n with m; auto. apply extensionality; auto.
  Qed.

  Lemma xelements_remove:
    forall A v (m: t A) i j,
    get i m = Some v ->
    exists l1 l2,
    xelements m j = l1 ++ (prev (prev_append i j), v) :: l2
    /\ xelements (remove i m) j = l1 ++ l2.
  Proof.
    intros A; induction m using tree_ind; intros.
  - discriminate.
  - assert (REMOVE: remove i (Node l o r) =
                    match i with
                    | xH => Node l None r
                    | xO ii => Node (remove ii l) o r
                    | xI ii => Node l o (remove ii r)
                    end).
    { destruct l, o, r, i; reflexivity. }
    rewrite gNode in H0. rewrite REMOVE. destruct i; rewrite ! xelements_Node.
    + destruct (IHm0 i (xI j) H0) as (l1 & l2 & EQ & EQ').
      exists (xelements l (xO j) ++
              match o with None => nil | Some x => (prev j, x) :: nil end ++
              l1);
      exists l2; split.
      rewrite EQ, ! app_ass. auto.
      rewrite EQ', ! app_ass. auto.
    + destruct (IHm i (xO j) H0) as (l1 & l2 & EQ & EQ').
      exists l1;
      exists (l2 ++
              match o with None => nil | Some x => (prev j, x) :: nil end ++
              xelements r (xI j));
      split.
      rewrite EQ, ! app_ass. auto.
      rewrite EQ', ! app_ass. auto.
    + subst o. exists (xelements l (xO j)); exists (xelements r (xI j)); split.
      rewrite prev_append_prev. auto.
      auto.
  Qed.

  Theorem elements_remove:
    forall A i v (m: t A),
    get i m = Some v ->
    exists l1 l2, elements m = l1 ++ (i,v) :: l2 /\ elements (remove i m) = l1 ++ l2.
  Proof.
    intros. exploit xelements_remove. eauto. instantiate (1 := xH).
    rewrite prev_append_prev. auto.
  Qed.

(** ** Folding over a tree *)

  Fixpoint fold' {A B} (f: B -> positive -> A -> B)
                 (i: positive) (m: tree' A) (v: B) {struct m} : B :=
    match m with
    | Node001 r => fold' f (xI i) r v
    | Node010 x => f v (prev i) x
    | Node011 x r => fold' f (xI i) r (f v (prev i) x)
    | Node100 l => fold' f (xO i) l v
    | Node101 l r => fold' f (xI i) r (fold' f (xO i) l v)
    | Node110 l x => f (fold' f (xO i) l v) (prev i) x
    | Node111 l x r => fold' f (xI i) r (f (fold' f (xO i) l v) (prev i) x)
    end.

  Definition fold {A B} (f: B -> positive -> A -> B) (m: t A) (v: B) :=
   match m with Empty => v | Nodes m' => fold' f xH m' v end.

  Lemma fold'_xelements':
    forall A B (f: B -> positive -> A -> B) m i v l,
    List.fold_left (fun a p => f a (fst p) (snd p)) l (fold' f i m v) =
    List.fold_left (fun a p => f a (fst p) (snd p)) (xelements' m i l) v.
  Proof.
    induction m; intros; simpl; auto.
    rewrite <- IHm1, <- IHm2; auto.
    rewrite <- IHm; auto.
    rewrite <- IHm1. simpl. rewrite <- IHm2; auto.
  Qed.

  Theorem fold_spec:
    forall A B (f: B -> positive -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  Proof.
    intros. unfold fold, elements. destruct m; auto. rewrite <- fold'_xelements'. auto.
  Qed.

  Fixpoint fold1' {A B} (f: B -> A -> B) (m: tree' A) (v: B) {struct m} : B :=
    match m with
    | Node001 r => fold1' f r v
    | Node010 x => f v x
    | Node011 x r => fold1' f r (f v x)
    | Node100 l => fold1' f l v
    | Node101 l r => fold1' f r (fold1' f l v)
    | Node110 l x => f (fold1' f l v) x
    | Node111 l x r => fold1' f r (f (fold1' f l v) x)
    end.


  Definition fold1 {A B} (f: B -> A -> B) (m: t A) (v: B) : B :=
    match m with Empty => v | Nodes m' => fold1' f m' v end.

  Lemma fold1'_xelements':
    forall A B (f: B -> A -> B) m i v l,
    List.fold_left (fun a p => f a (snd p)) l (fold1' f m v) =
    List.fold_left (fun a p => f a (snd p)) (xelements' m i l) v.
  Proof.
    induction m; simpl; intros; auto.
    rewrite <- IHm1. rewrite <- IHm2. auto.
    rewrite <- IHm. auto. 
    rewrite <- IHm1. simpl. rewrite <- IHm2. auto.
  Qed.

  Theorem fold1_spec:
    forall A B (f: B -> A -> B) (v: B) (m: t A),
    fold1 f m v =
    List.fold_left (fun a p => f a (snd p)) (elements m) v.
  Proof.
    intros. destruct m as [|m]. reflexivity.
    apply fold1'_xelements' with (l := @nil (positive * A)).
  Qed.

  Arguments empty A : simpl never.
  Arguments get {A} p m : simpl never.
  Arguments set {A} p x m : simpl never.
  Arguments remove {A} p m : simpl never.

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
    intros. reflexivity.
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
  Parameter t: Type.
  Parameter index: t -> positive.
  Axiom index_inj: forall (x y: t), index x = index y -> x = y.
  Parameter eq: forall (x y: t), {x = y} + {x <> y}.
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
  Parameter t: Type.
  Parameter eq: forall (x y: t), {x = y} + {x <> y}.
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

(** * A partial implementation of trees over any type that injects into type [positive] *)

Module ITree(X: INDEXED_TYPE).

  Definition elt := X.t.
  Definition elt_eq := X.eq.
  Definition t : Type -> Type := PTree.t.

  Definition empty (A: Type): t A := PTree.empty A.
  Definition get (A: Type) (k: elt) (m: t A): option A := PTree.get (X.index k) m.
  Definition set (A: Type) (k: elt) (v: A) (m: t A): t A := PTree.set (X.index k) v m.
  Definition remove (A: Type) (k: elt) (m: t A): t A := PTree.remove (X.index k) m.

  Theorem gempty:
    forall (A: Type) (i: elt), get i (empty A) = None.
  Proof.
    intros. apply PTree.gempty.
  Qed.
  Theorem gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Proof.
    intros. apply PTree.gss.
  Qed.
  Theorem gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. apply PTree.gso. red; intros; elim H; apply X.index_inj; auto.
  Qed.
  Theorem gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Proof.
    intros. destruct (elt_eq i j). subst j; apply gss. apply gso; auto.
  Qed.
  Theorem grs:
    forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Proof.
    intros. apply PTree.grs.
  Qed.
  Theorem gro:
    forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Proof.
    intros. apply PTree.gro. red; intros; elim H; apply X.index_inj; auto.
  Qed.
  Theorem grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof.
    intros. destruct (elt_eq i j). subst j; apply grs. apply gro; auto.
  Qed.

  Definition beq: forall (A: Type), (A -> A -> bool) -> t A -> t A -> bool := PTree.beq.
  Theorem beq_sound:
    forall (A: Type) (eqA: A -> A -> bool) (t1 t2: t A),
    beq eqA t1 t2 = true ->
    forall (x: elt),
     match get x t1, get x t2 with
     | None, None => True
     | Some y1, Some y2 => eqA y1 y2 = true
     | _, _ => False
    end.
  Proof.
    unfold beq, get. intros. rewrite PTree.beq_correct in H. apply H.
  Qed.

  Definition combine: forall (A B C: Type), (option A -> option B -> option C) -> t A -> t B -> t C := PTree.combine.
  Theorem gcombine:
    forall (A B C: Type) (f: option A -> option B -> option C),
    f None None = None ->
    forall (m1: t A) (m2: t B) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).
  Proof.
    intros. apply PTree.gcombine. auto.
  Qed.
End ITree.

Module ZTree := ITree(ZIndexed).

(** * Additional properties over trees *)

Require Import Equivalence EquivDec.

Module Tree_Properties(T: TREE).

(** Two induction principles over [fold]. *)

Section TREE_FOLD_IND.

Variables V A: Type.
Variable f: A -> T.elt -> V -> A.
Variable P: T.t V -> A -> Type.
Variable init: A.
Variable m_final: T.t V.

Hypothesis H_base:
  forall m,
  (forall k, T.get k m = None) ->
  P m init.

Hypothesis H_rec:
  forall m a k v,
  T.get k m = Some v -> T.get k m_final = Some v ->
  P (T.remove k m) a -> P m (f a k v).

Let f' (p : T.elt * V) (a: A) := f a (fst p) (snd p).

Let P' (l: list (T.elt * V)) (a: A) : Type :=
  forall m, (forall k v, In (k, v) l <-> T.get k m = Some v) -> P m a.

Let H_base':
  P' nil init.
Proof.
  intros m EQV. apply H_base.
  intros. destruct (T.get k m) as [v|] eqn:G; auto.
  apply EQV in G. contradiction.
Qed.

Let H_rec':
  forall k v l a,
  ~In k (List.map fst l) ->
  T.get k m_final = Some v ->
  P' l a ->
  P' ((k, v) :: l) (f a k v).
Proof.
  unfold P'; intros k v l a NOTIN FINAL HR m EQV.
  set (m0 := T.remove k m).
  apply H_rec.
- apply EQV. simpl; auto.
- auto.
- apply HR. intros k' v'. rewrite T.grspec. split; intros; destruct (T.elt_eq k' k).
  + subst k'. elim NOTIN. change k with (fst (k, v')). apply List.in_map; auto.
  + apply EQV. simpl; auto.
  + congruence.
  + apply EQV in H. simpl in H. intuition congruence.
Qed.

Lemma fold_ind_aux:
  forall l,
  (forall k v, In (k, v) l -> T.get k m_final = Some v) ->
  list_norepet (List.map fst l) ->
  P' l (List.fold_right f' init l).
Proof.
  induction l as [ | [k v] l ]; simpl; intros FINAL NOREPET.
- apply H_base'.
- apply H_rec'.
  + inv NOREPET. auto.
  + apply FINAL. auto.
  + apply IHl. auto. inv NOREPET; auto.
Defined.

Theorem fold_ind:
  P m_final (T.fold f m_final init).
Proof.
  intros.
  set (l' := List.rev (T.elements m_final)).
  assert (P' l' (List.fold_right f' init l')).
  { apply fold_ind_aux.
    intros. apply T.elements_complete. apply List.in_rev. auto.
    unfold l'; rewrite List.map_rev. apply list_norepet_rev. apply T.elements_keys_norepet. }
  unfold l', f' in X; rewrite fold_left_rev_right in X.
  rewrite T.fold_spec. apply X.
  intros; simpl. rewrite <- List.in_rev.
  split. apply T.elements_complete. apply T.elements_correct.
Defined.

End TREE_FOLD_IND.

Section TREE_FOLD_REC.

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

Theorem fold_rec:
  P m_final (T.fold f m_final init).
Proof.
  apply fold_ind. 
- intros. apply P_compat with (T.empty V); auto.
  + intros. rewrite T.gempty. auto.
- intros. apply P_compat with (T.set k v (T.remove k m)).
  + intros. rewrite T.gsspec, T.grspec. destruct (T.elt_eq x k); auto. congruence.
  + apply H_rec; auto. apply T.grs.
Qed.

End TREE_FOLD_REC.

(** A nonnegative measure over trees *)

Section MEASURE.

Variable V: Type.

Definition cardinal (x: T.t V) : nat := List.length (T.elements x).

Theorem cardinal_remove:
  forall x m y, T.get x m = Some y -> (cardinal (T.remove x m) < cardinal m)%nat.
Proof.
  unfold cardinal; intros.
  exploit T.elements_remove; eauto. intros (l1 & l2 & P & Q).
  rewrite P, Q. rewrite ! app_length. simpl. lia.
Qed.

Theorem cardinal_set:
  forall x m y, T.get x m = None -> (cardinal m < cardinal (T.set x y m))%nat.
Proof.
  intros. set (m' := T.set x y m).
  replace (cardinal m) with (cardinal (T.remove x m')).
  apply cardinal_remove with y. unfold m'; apply T.gss.
  unfold cardinal. f_equal. apply T.elements_extensional.
  intros. unfold m'. rewrite T.grspec, T.gsspec.
  destruct (T.elt_eq i x); auto. congruence.
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

Global Instance Equal_Equivalence : Equivalence Equal := {
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

Global Instance Equal_EqDec : EqDec (T.t A) Equal := Equal_dec.

End EXTENSIONAL_EQUALITY.

(** Creating a tree from a list of (key, value) pairs. *)

Section OF_LIST.

Variable A: Type.

Let f := fun (m: T.t A) (k_v: T.elt * A) => T.set (fst k_v) (snd k_v) m.

Definition of_list (l: list (T.elt * A)) : T.t A :=
  List.fold_left f l (T.empty _).

Lemma in_of_list:
  forall l k v, T.get k (of_list l) = Some v -> In (k, v) l.
Proof.
  assert (REC: forall k v l m,
           T.get k (fold_left f l m) = Some v -> In (k, v) l \/ T.get k m = Some v).
  { induction l as [ | [k1 v1] l]; simpl; intros.
  - tauto.
  - apply IHl in H. unfold f in H. simpl in H. rewrite T.gsspec in H.
    destruct H; auto.
    destruct (T.elt_eq k k1). inv H. auto. auto.
  }
  intros. apply REC in H. rewrite T.gempty in H. intuition congruence.
Qed.

Lemma of_list_dom:
  forall l k, In k (map fst l) -> exists v, T.get k (of_list l) = Some v.
Proof.
  assert (REC: forall k l m,
            In k (map fst l) \/ (exists v, T.get k m = Some v) ->
            exists v, T.get k (fold_left f l m) = Some v).
  { induction l as [ | [k1 v1] l]; simpl; intros.
  - tauto.
  - apply IHl. unfold f; rewrite T.gsspec. simpl. destruct (T.elt_eq k k1).
    right; econstructor; eauto.
    intuition congruence.
  }
  intros. apply REC. auto.
Qed.

Remark of_list_unchanged:
  forall k l m, ~In k (map fst l) -> T.get k (List.fold_left f l m) = T.get k m.
Proof.
  induction l as [ | [k1 v1] l]; simpl; intros.
- auto.
- rewrite IHl by tauto. unfold f; apply T.gso; intuition auto.
Qed.

Lemma of_list_unique:
  forall k v l1 l2,
  ~In k (map fst l2) -> T.get k (of_list (l1 ++ (k, v) :: l2)) = Some v.
Proof.
  intros. unfold of_list. rewrite fold_left_app. simpl.
  rewrite of_list_unchanged by auto. unfold f; apply T.gss.
Qed.

Lemma of_list_norepet:
  forall l k v, list_norepet (map fst l) -> In (k, v) l -> T.get k (of_list l) = Some v.
Proof.
  assert (REC: forall k v l m,
            list_norepet (map fst l) ->
            In (k, v) l ->
            T.get k (fold_left f l m) = Some v).
  { induction l as [ | [k1 v1] l]; simpl; intros.
    contradiction.
    inv H. destruct H0.
    inv H. rewrite of_list_unchanged by auto. apply T.gss.
    apply IHl; auto.
  }
  intros; apply REC; auto.
Qed.

Lemma of_list_elements:
  forall m k, T.get k (of_list (T.elements m)) = T.get k m.
Proof.
  intros. destruct (T.get k m) as [v|] eqn:M.
- apply of_list_norepet. apply T.elements_keys_norepet. apply T.elements_correct; auto.
- destruct (T.get k (of_list (T.elements m))) as [v|] eqn:M'; auto.
  apply in_of_list in M'. apply T.elements_complete in M'. congruence.
Qed.

End OF_LIST.

Lemma of_list_related:
  forall (A B: Type) (R: A -> B -> Prop) k l1 l2,
  list_forall2 (fun ka kb => fst ka = fst kb /\ R (snd ka) (snd kb)) l1 l2 ->
  option_rel R (T.get k (of_list l1)) (T.get k (of_list l2)).
Proof.
  intros until k. unfold of_list.
  set (R' := fun ka kb => fst ka = fst kb /\ R (snd ka) (snd kb)).
  set (fa := fun (m : T.t A) (k_v : T.elt * A) => T.set (fst k_v) (snd k_v) m).
  set (fb := fun (m : T.t B) (k_v : T.elt * B) => T.set (fst k_v) (snd k_v) m).
  assert (REC: forall l1 l2, list_forall2 R' l1 l2 ->
               forall m1 m2, option_rel R (T.get k m1) (T.get k m2) ->
               option_rel R (T.get k (fold_left fa l1 m1)) (T.get k (fold_left fb l2 m2))).
  { induction 1; intros; simpl.
  - auto.
  - apply IHlist_forall2. unfold fa, fb. rewrite ! T.gsspec.
    destruct H as [E F]. rewrite E. destruct (T.elt_eq k (fst b1)).
    constructor; auto.
    auto. }
  intros. apply REC; auto. rewrite ! T.gempty. constructor.
Qed.

End Tree_Properties.

Module PTree_Properties := Tree_Properties(PTree).

(** * Useful notations *)

Notation "a ! b" := (PTree.get b a) (at level 1).
Notation "a !! b" := (PMap.get b a) (at level 1).

(** A purely functional union-find algorithm *)

Require Import Wf.

(** The ``union-find'' algorithm is used to represent equivalence classes
  over a given type.  It maintains a data structure representing a partition
  of the type into equivalence classes. Three operations are provided:
- [empty], which returns the finest partition: each element of the type
  is equivalent to itself only.
- [repr part x] returns a canonical representative for the equivalence
  class of element [x] in partition [part].  Two elements [x] and [y] 
  are in the same equivalence class if and only if
  [repr part x = repr part y].
- [identify part x y] returns a new partition where the equivalence
  classes of [x] and [y] are merged, and all equivalences valid in [part]
  are still valid.

  The partitions are represented by partial mappings from elements 
  to elements.  If [part] maps [x] to [y], this means that [x] and [y]
  are in the same equivalence class.  The canonical representative
  of the class of [x] is obtained by iteratively following these mappings
  until an element not mapped to anything is reached; this element is the
  canonical representative, as returned by [repr].

  In algorithm textbooks, the mapping is maintained imperatively by
  storing pointers within elements.  Here, we give a purely functional
  presentation where the mapping is a separate functional data structure.
*)

Ltac CaseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

Ltac IntroElim :=
  match goal with
  |  |- (forall id : exists x : _, _, _) =>
      intro id; elim id; clear id; IntroElim
  |  |- (forall id : _ /\ _, _) => intro id; elim id; clear id; IntroElim
  |  |- (forall id : _ \/ _, _) => intro id; elim id; clear id; IntroElim
  |  |- (_ -> _) => intro; IntroElim
  | _ => idtac
  end.

Ltac MyElim n := elim n; IntroElim.

(** The elements of equivalence classes are represented by the following
  signature: a type with a decidable equality. *)

Module Type ELEMENT.
  Variable T: Set.
  Variable eq: forall (a b: T), {a = b} + {a <> b}.
End ELEMENT.

(** The mapping structure over elements is represented by the following
  signature. *)

Module Type MAP.
  Variable elt: Set.
  Variable T: Set.
  Variable empty: T.
  Variable get: elt -> T -> option elt.
  Variable add: elt -> elt -> T -> T.

  Hypothesis get_empty: forall (x: elt), get x empty = None.
  Hypothesis get_add_1:
   forall (x y: elt) (m: T), get x (add x y m) = Some y.
  Hypothesis get_add_2:
   forall (x y z: elt) (m: T), z <> x -> get z (add x y m) = get z m.
End MAP.

(** Our implementation of union-find is a functor, parameterized by
  a structure for elements and a structure for maps.  It returns a
  module with the following structure. *)

Module Type UNIONFIND.
  Variable elt: Set.
  (** The type of partitions. *)
  Variable T: Set.

  (** The operations over partitions. *)
  Variable empty: T.
  Variable repr: T -> elt -> elt.
  Variable identify: T -> elt -> elt -> T.

  (** The relation implied by the partition [m]. *)
  Definition sameclass (m: T) (x y: elt) : Prop := repr m x = repr m y.

  (* [sameclass] is an equivalence relation *)
  Hypothesis sameclass_refl:
    forall (m: T) (x: elt), sameclass m x x.
  Hypothesis sameclass_sym:
    forall (m: T) (x y: elt), sameclass m x y -> sameclass m y x.
  Hypothesis sameclass_trans:
    forall (m: T) (x y z: elt),
    sameclass m x y -> sameclass m y z -> sameclass m x z.

  (* [repr m x] is a canonical representative of the equivalence class
     of [x] in partition [m]. *)
  Hypothesis repr_repr:
    forall (m: T) (x: elt), repr m (repr m x) = repr m x.
  Hypothesis sameclass_repr:
    forall (m: T) (x: elt), sameclass m x (repr m x).

  (* [empty] is the finest partition *)
  Hypothesis repr_empty:
    forall (x: elt), repr empty x = x.
  Hypothesis sameclass_empty:
    forall (x y: elt), sameclass empty x y -> x = y.

  (* [identify] preserves existing equivalences and adds an equivalence
     between the two elements provided. *)
  Hypothesis sameclass_identify_1:
    forall (m: T) (x y: elt), sameclass (identify m x y) x y.
  Hypothesis sameclass_identify_2:
    forall (m: T) (x y u v: elt),
    sameclass m u v -> sameclass (identify m x y) u v.

End UNIONFIND.

(** Implementation of the union-find algorithm. *)

Module Unionfind (E: ELEMENT) (M: MAP with Definition elt := E.T) 
          <: UNIONFIND with Definition elt := E.T.

Definition elt := E.T.

(* A set of equivalence classes over [elt] is represented by a map [m].
- [M.get a m = Some a'] means that [a] is in the same class as [a'].
- [M.get a m = None] means that [a] is the canonical representative
     for its equivalence class.
*)

(** Such a map induces an ordering over type [elt]:
   [repr_order m a a'] if and only if [M.get a' m = Some a].
   This ordering must be well founded (no cycles). *)

Definition repr_order (m: M.T) (a a': elt) : Prop :=
  M.get a' m = Some a.

(** The canonical representative of an element.  
  Needs Noetherian recursion. *)

Lemma option_sum:
  forall (x: option elt), {y: elt | x = Some y} + {x = None}.
Proof.
  intro x. case x.
  left. exists e. auto.
  right. auto.
Qed.

Definition repr_rec
  (m: M.T) (a: elt) (rec: forall b: elt, repr_order m b a -> elt) :=
     match option_sum (M.get a m) with
     | inleft (exist b P) => rec b P
     | inright _ => a
     end.

Definition repr_aux
    (m: M.T) (wf: well_founded (repr_order m)) (a: elt) : elt :=
  Fix wf (fun (_: elt) => elt) (repr_rec m) a.

Lemma repr_rec_ext:
  forall (m: M.T) (x: elt) (f g: forall y:elt, repr_order m y x -> elt),
  (forall (y: elt) (p: repr_order m y x), f y p = g y p) ->
  repr_rec m x f = repr_rec m x g.
Proof.
  intros. unfold repr_rec. 
  case (option_sum (M.get x m)).
  intros. elim s; intros. apply H.
  intros. auto.
Qed.

Lemma repr_aux_none:
  forall (m: M.T) (wf: well_founded (repr_order m)) (a: elt),
  M.get a m = None ->
  repr_aux m wf a = a.
Proof.
  intros. 
  generalize (Fix_eq wf (fun (_:elt) => elt) (repr_rec m) (repr_rec_ext m) a). 
  intro. unfold repr_aux. rewrite H0. 
  unfold repr_rec. 
  case (option_sum (M.get a m)).
  intro s; elim s; intros.
  rewrite H in p; discriminate.
  intros. auto.
Qed.

Lemma repr_aux_some:
  forall (m: M.T) (wf: well_founded (repr_order m)) (a a': elt),
  M.get a m = Some a' ->
  repr_aux m wf a = repr_aux m wf a'.
Proof.
  intros. 
  generalize (Fix_eq wf (fun (_:elt) => elt) (repr_rec m) (repr_rec_ext m) a). 
  intro. unfold repr_aux. rewrite H0. unfold repr_rec.
  case (option_sum (M.get a m)).
  intro s; elim s; intros.
  rewrite H in p. injection p; intros. rewrite H1. auto.
  intros. rewrite H in e. discriminate.
Qed.
 
Lemma repr_aux_canon:
  forall (m: M.T) (wf: well_founded (repr_order m)) (a: elt),
  M.get (repr_aux m wf a) m = None.
Proof.
  intros.
  apply (well_founded_ind wf (fun (a: elt) => M.get (repr_aux m wf a) m = None)).
  intros.
  generalize (Fix_eq wf (fun (_:elt) => elt) (repr_rec m) (repr_rec_ext m) x). 
  intro. unfold repr_aux. rewrite H0. 
  unfold repr_rec.
  case (option_sum (M.get x m)).
  intro s; elim s; intros. 
  unfold repr_aux in H. apply H.
  unfold repr_order. auto.
  intro. auto.
Qed.

(** The empty partition (each element in its own class) is well founded. *)

Lemma wf_empty:
  well_founded (repr_order M.empty).
Proof.
  red. intro. apply Acc_intro.
  intros b RO.
  red in RO.
  rewrite M.get_empty in RO.
  discriminate.
Qed.

(** Merging two equivalence classes. *)

Section IDENTIFY.

Variable m: M.T.
Hypothesis mwf: well_founded (repr_order m).
Variable a b: elt.
Hypothesis a_diff_b: a <> b.
Hypothesis a_canon: M.get a m = None.
Hypothesis b_canon: M.get b m = None.

(** Identifying two distinct canonical representatives [a] and [b] 
  is achieved by mapping one to the other. *)

Definition identify_base: M.T := M.add a b m.

Lemma identify_base_b_canon:
  M.get b identify_base = None.
Proof.
  unfold identify_base.
  rewrite M.get_add_2.
  auto.
  apply sym_not_eq. auto.
Qed.

Lemma identify_base_a_maps_to_b:
  M.get a identify_base = Some b.
Proof.
  unfold identify_base. rewrite M.get_add_1. auto.
Qed.

Lemma identify_base_repr_order:
  forall (x y: elt),
  repr_order identify_base x y ->
  repr_order m x y \/ (y = a /\ x = b).
Proof.
  intros x y. unfold identify_base.
  unfold repr_order.
  case (E.eq a y); intro.
  rewrite e. rewrite M.get_add_1.
  intro. injection H. intro. rewrite H0. tauto.
  rewrite M.get_add_2; auto.
Qed.

(** [identify_base] preserves well foundation. *)

Lemma identify_base_order_wf:
  well_founded (repr_order identify_base).
Proof.
  red. 
  cut (forall (x: elt), Acc (repr_order m) x -> Acc (repr_order identify_base) x).
  intro CUT. intro x. apply CUT. apply mwf.

  induction 1.
  apply Acc_intro. intros.
  MyElim (identify_base_repr_order y x H1).
  apply H0; auto.
  rewrite H3.
  apply Acc_intro.
  intros z H4.
  red in H4. rewrite identify_base_b_canon in H4. discriminate.
Qed.

Lemma identify_aux_decomp:
  forall (x: elt),
     (M.get x m = None /\ M.get x identify_base = None)
  \/ (x = a /\ M.get x m = None /\ M.get x identify_base = Some b)
  \/ (exists y, M.get x m = Some y /\ M.get x identify_base = Some y).
Proof.
  intro x.
  unfold identify_base.
  case (E.eq a x); intro.
  rewrite <- e. rewrite M.get_add_1.
  tauto.
  rewrite M.get_add_2; auto.
  case (M.get x m); intros.
  right; right; exists e; tauto.
  tauto.
Qed.

Lemma identify_base_repr:
  forall (x: elt),
  repr_aux identify_base identify_base_order_wf x =
  (if E.eq (repr_aux m mwf x) a then b else repr_aux m mwf x).
Proof.
  intro x0.
  apply (well_founded_ind mwf
    (fun (x: elt) =>
      repr_aux identify_base identify_base_order_wf x =
      (if E.eq (repr_aux m mwf x) a then b else repr_aux m mwf x)));
  intros.
  MyElim (identify_aux_decomp x).

  rewrite (repr_aux_none identify_base).
  rewrite (repr_aux_none m mwf x).
  case (E.eq x a); intro.
  subst x.
  rewrite identify_base_a_maps_to_b in H1.
  discriminate.
  auto. auto. auto.

  subst x. rewrite (repr_aux_none m mwf a); auto.
  case (E.eq a a); intro.
  rewrite (repr_aux_some identify_base identify_base_order_wf a b).
  rewrite (repr_aux_none identify_base identify_base_order_wf b).
  auto. apply identify_base_b_canon. auto. 
  tauto.

  rewrite (repr_aux_some identify_base identify_base_order_wf x x1); auto.
  rewrite (repr_aux_some m mwf x x1); auto.
Qed.

Lemma identify_base_sameclass_1:
  forall (x y: elt),
  repr_aux m mwf x = repr_aux m mwf y ->
  repr_aux identify_base identify_base_order_wf x =
    repr_aux identify_base identify_base_order_wf y.
Proof.
  intros.
  rewrite identify_base_repr.
  rewrite identify_base_repr.
  rewrite H.
  auto.
Qed.

Lemma identify_base_sameclass_2:
  forall (x y: elt),
  repr_aux m mwf x = a ->
  repr_aux m mwf y = b ->
  repr_aux identify_base identify_base_order_wf x =
  repr_aux identify_base identify_base_order_wf y.
Proof.
  intros.
  rewrite identify_base_repr.
  rewrite identify_base_repr.
  rewrite H. 
  case (E.eq a a); intro.
  case (E.eq (repr_aux m mwf y) a); auto.
  tauto.
Qed.

End IDENTIFY.

(** The union-find data structure is a record encapsulating a mapping
  and a proof of well foundation. *)

Record unionfind : Set := mkunionfind
  { map: M.T; wf: well_founded (repr_order map) }.

Definition T := unionfind.

Definition repr (uf: unionfind) (a: elt) : elt :=
  repr_aux (map uf) (wf uf) a.

Lemma repr_repr:
  forall (uf: unionfind) (a: elt), repr uf (repr uf a) = repr uf a.
Proof.
  intros.
  unfold repr.
  rewrite (repr_aux_none (map uf) (wf uf) (repr_aux (map uf) (wf uf) a)).
  auto.
  apply repr_aux_canon. 
Qed.

Definition empty := mkunionfind M.empty wf_empty.

(** [identify] computes canonical representatives for the two elements
  and adds a mapping from one to the other, unless they are already
  equal. *)

Definition identify (uf: unionfind) (a b: elt) : unionfind :=
  match E.eq (repr uf a) (repr uf b) with
  | left EQ =>
      uf
  | right NOTEQ =>
      mkunionfind
        (identify_base (map uf) (repr uf a) (repr uf b))
        (identify_base_order_wf (map uf) (wf uf)
            (repr uf a) (repr uf b)
            NOTEQ
            (repr_aux_canon (map uf) (wf uf) b))
  end.

Definition sameclass (uf: unionfind) (a b: elt) : Prop :=
  repr uf a = repr uf b.

Lemma sameclass_refl:
  forall (uf: unionfind) (a: elt), sameclass uf a a.
Proof.
  intros. red. auto.
Qed.

Lemma sameclass_sym:
  forall (uf: unionfind) (a b: elt), sameclass uf a b -> sameclass uf b a.
Proof.
  intros. red. symmetry. exact H.
Qed.

Lemma sameclass_trans:
  forall (uf: unionfind) (a b c: elt),
  sameclass uf a b -> sameclass uf b c -> sameclass uf a c.
Proof.
  intros. red. transitivity (repr uf b). exact H. exact H0.
Qed.

Lemma sameclass_repr:
  forall (uf: unionfind) (a: elt), sameclass uf a (repr uf a).
Proof.
  intros. red. symmetry. rewrite repr_repr. auto.
Qed.

Lemma repr_empty:
  forall (a: elt), repr empty a = a.
Proof.
  intro a. unfold repr; unfold empty.
  simpl.
  apply repr_aux_none.
  apply M.get_empty.
Qed.

Lemma sameclass_empty:
  forall (a b: elt), sameclass empty a b -> a = b.
Proof.
  intros. red in H. rewrite repr_empty in H.
  rewrite repr_empty in H. auto.
Qed.

Lemma sameclass_identify_2:
  forall (uf: unionfind) (a b x y: elt),
  sameclass uf x y -> sameclass (identify uf a b) x y.
Proof.
  intros.
  unfold identify.
  case (E.eq (repr uf a) (repr uf b)).
  intro. auto.
  intros; red; unfold repr; simpl.
  apply identify_base_sameclass_1.
  apply repr_aux_canon.
  exact H.
Qed.

Lemma sameclass_identify_1:
  forall (uf: unionfind) (a b: elt),
  sameclass (identify uf a b) a b.
Proof.
  intros.
  unfold identify.
  case (E.eq (repr uf a) (repr uf b)).
  intro. auto.
  intros.
  red; unfold repr; simpl.
  apply identify_base_sameclass_2.
  apply repr_aux_canon.
  auto.
  auto.
Qed.

End Unionfind.

(* Example of use 1: with association lists *)

(*

Require Import List.

Module AListMap(E: ELEMENT) : MAP.

Definition elt := E.T.
Definition T := list (elt * elt).
Definition empty : T := nil.
Fixpoint get (x: elt) (m: T) {struct m} : option elt :=
  match m with
  | nil => None
  | (a,b) :: t =>
      match E.eq x a with
      | left _ => Some b
      | right _ => get x t
      end
  end.
Definition add (x y: elt) (m: T) := (x,y) :: m.

Lemma get_empty: forall (x: elt), get x empty = None.
Proof.
  intro. unfold empty. simpl. auto.
Qed.

Lemma get_add_1:
  forall (x y: elt) (m: T), get x (add x y m) = Some y.
Proof.
  intros. unfold add. simpl. 
  case (E.eq x x); intro.
  auto.
  tauto.
Qed.

Lemma get_add_2:
   forall (x y z: elt) (m: T), z <> x -> get z (add x y m) = get z m.
Proof.
  intros. unfold add. simpl.
  case (E.eq z x); intro.
  subst z; tauto.
  auto.
Qed.

End AListMap.

*)


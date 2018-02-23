Require Import String.
Require Import FSets.
Require Import Coqlib.
Require Import Maps.
Require Import Ordered.

(** The mapping between the external representation of identifiers as
  [string]s and their internal representation as [ident]s is axiomatized
  as a bijection, and constructed incrementally by Camlcoq.ml.

  In the future we may want to have an alternative implementation the
  [IDENT] interface entirely in Coq, which the user could choose at
  [./configure] time depending on their needs. Such an implementation
  would have to forgo string interning and use less efficient
  primitives, but would compute within Coq and avoid relying on
  trusted ML code. *)

Module Type IDENT.
  Parameter t: Type.
  Parameter eq: forall i j: t, {i = j} + {i <> j}.
  Parameter of_string: string -> t.
  Parameter to_string: t -> string.
  Parameter lt: t -> t -> Prop.
  Parameter compare: t -> t -> comparison.

  Axiom of_to_string: forall i, of_string (to_string i) = i.
  Axiom to_of_string: forall s, to_string (of_string s) = s.

  Axiom lt_trans: forall i j k, lt i j -> lt j k -> lt i k.
  Axiom lt_not_eq: forall i j, lt i j -> i <> j.

  Axiom compare_spec:
    forall i j, CompareSpec (i = j) (lt i j) (lt j i) (compare i j).

  Declare Module Tree : TREE
    with Definition elt := t
    with Definition elt_eq := eq.

  (** This is a temporary workaround to enable the hack in Initializers.v,
    whereby identifiers are stored in the [block] components of pointers.
    We can remove it if we merge PR #220 or something such. *)
  Parameter to_positive: t -> positive.
  Parameter of_positive: positive -> t.
  Axiom of_to_positive: forall p, of_positive (to_positive p) = p.
End IDENT.

Module Ident : IDENT.
  Definition t := positive.
  Definition eq := peq.
  Definition lt := Pos.lt.
  Definition compare := Pos.compare.
  Definition lt_trans := Pos.lt_trans.
  Definition compare_spec := Pos.compare_spec.

  Lemma lt_not_eq i j:
    lt i j -> i <> j.
  Proof.
    intros H Hij. subst.
    eapply Pos.lt_irrefl; eauto.
  Qed.

  Module Tree := PTree.

  Parameter of_string: string -> t.
  Parameter to_string: t -> string.

  Axiom of_to_string: forall i, of_string (to_string i) = i.
  Axiom to_of_string: forall s, to_string (of_string s) = s.

  Definition to_positive i: t := i.
  Definition of_positive i: t := i.
  Definition of_to_positive i: to_positive (of_positive i) = i := eq_refl.
End Ident.

Module OrderedIdent <: OrderedType.
  Definition t := Ident.t.
  Definition eq := @eq Ident.t.
  Definition lt := Ident.lt.
  Definition eq_dec := Ident.eq.
  Definition eq_refl := @eq_refl Ident.t.
  Definition eq_trans := @eq_trans Ident.t.
  Definition eq_sym := @eq_sym Ident.t.
  Definition lt_trans := Ident.lt_trans.
  Definition lt_not_eq := Ident.lt_not_eq.

  Program Definition compare x y: Compare lt eq x y :=
    match Ident.compare x y with Lt => LT _ | Eq => EQ _ | Gt => GT _ end.
  Next Obligation.
    destruct (Ident.compare_spec x y); try discriminate; eauto.
  Qed.
  Next Obligation.
    destruct (Ident.compare_spec x y); try discriminate; eauto.
  Qed.
  Next Obligation.
    destruct (Ident.compare_spec x y); try discriminate; eauto.
  Qed.
End OrderedIdent.

Lemma ident_of_string_inj s t:
  Ident.of_string s = Ident.of_string t -> s = t.
Proof.
  intros Hst.
  rewrite <- (Ident.to_of_string s).
  rewrite <- (Ident.to_of_string t).
  congruence.
Qed.

Module ATree := Ident.Tree.
Module ATree_Properties := Tree_Properties ATree.
Notation "a $ b" := (ATree.get b a) (at level 1).

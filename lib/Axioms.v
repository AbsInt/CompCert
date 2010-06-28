Require ClassicalFacts.

(* We use just 2 axioms of extensionality:

1.  Functional extensionality for dependent functions
  (FunctionalExtensionality.functional_extensionality_dep)
   forall {A} {B : A -> Type},   forall (f g : forall x : A, B x), (forall x, f x = g x) -> f = g.

2.  Propositional extensionality  (forall A B:Prop, (A <-> B) -> A = B.)

*)

Require Export FunctionalExtensionality.  (* Contains one Axiom *)

Axiom prop_ext: ClassicalFacts.prop_extensionality.
Implicit Arguments prop_ext.

Lemma proof_irr: ClassicalFacts.proof_irrelevance.
Proof.
exact (ClassicalFacts.ext_prop_dep_proof_irrel_cic prop_ext).
Qed.
Implicit Arguments proof_irr.

Lemma extensionality:
 forall (A B: Type) (f g : A -> B),  (forall x, f x = g x) -> f = g.
Proof. intros; apply functional_extensionality. auto. Qed.
Implicit Arguments extensionality.

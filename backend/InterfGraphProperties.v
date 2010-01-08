Require Import InterfGraph.
Require Import Coloring.

Lemma set_reg_reg_diff_ext : forall x f live live0,
SetRegReg.In x (interf_reg_reg (interf_graph f live live0)) -> fst x <> snd x.

Proof.
Admitted.
(** Representation of interference graphs for register allocation. *)

Require Import Coqlib.
Require Import FSet.
Require Import Maps.
Require Import Ordered.
Require Import Registers.
Require Import Locations.

(** Interference graphs are undirected graphs with two kinds of nodes:
- RTL pseudo-registers;
- Machine registers.

and four kind of edges:
- Conflict edges between two pseudo-registers.
  (Meaning: these two pseudo-registers must not be assigned the same
   location.)
- Conflict edges between a pseudo-register and a machine register
  (Meaning: this pseudo-register must not be assigned this machine
   register.)
- Preference edges between two pseudo-registers.
  (Meaning: the generated code would be more efficient if those two
   pseudo-registers were assigned the same location, but if this is not
   possible, the generated code will still be correct.)
- Preference edges between a pseudo-register and a machine register
  (Meaning: the generated code would be more efficient if this
   pseudo-register was assigned this machine register, but if this is not
   possible, the generated code will still be correct.)

A graph is represented by four finite sets of edges (one of each kind
above).  An edge is represented by a pair of two pseudo-registers or
a pair (pseudo-register, machine register).  
In the case of two pseudo-registers ([r1], [r2]), we adopt the convention
that [r1] <= [r2], so as to reflect the undirected nature of the edge.
*)

Module OrderedReg <: OrderedType with Definition t := reg := OrderedPositive.
Module OrderedRegReg := OrderedPair(OrderedReg)(OrderedReg).
Module OrderedMreg := OrderedIndexed(IndexedMreg).
Module OrderedRegMreg := OrderedPair(OrderedReg)(OrderedMreg).

Module SetDepRegReg := FSetAVL.Make(OrderedRegReg).
Module SetRegReg := NodepOfDep(SetDepRegReg).
Module SetDepRegMreg := FSetAVL.Make(OrderedRegMreg).
Module SetRegMreg := NodepOfDep(SetDepRegMreg).

Record graph: Set := mkgraph {
  interf_reg_reg: SetRegReg.t;
  interf_reg_mreg: SetRegMreg.t;
  pref_reg_reg: SetRegReg.t;
  pref_reg_mreg: SetRegMreg.t
}.

Definition empty_graph :=
  mkgraph SetRegReg.empty SetRegMreg.empty
          SetRegReg.empty SetRegMreg.empty.

(** The following functions add a new edge (if not already present)
  to the given graph. *)

Definition ordered_pair (x y: reg) :=
  if plt x y then (x, y) else (y, x).

Definition add_interf (x y: reg) (g: graph) :=
  mkgraph (SetRegReg.add (ordered_pair x y) g.(interf_reg_reg))
          g.(interf_reg_mreg)
          g.(pref_reg_reg)
          g.(pref_reg_mreg).

Definition add_interf_mreg  (x: reg) (y: mreg) (g: graph) :=
  mkgraph g.(interf_reg_reg)
          (SetRegMreg.add (x, y) g.(interf_reg_mreg))
          g.(pref_reg_reg)
          g.(pref_reg_mreg).

Definition add_pref (x y: reg) (g: graph) :=
  mkgraph g.(interf_reg_reg)
          g.(interf_reg_mreg)
          (SetRegReg.add (ordered_pair x y) g.(pref_reg_reg))
          g.(pref_reg_mreg).

Definition add_pref_mreg  (x: reg) (y: mreg) (g: graph) :=
  mkgraph g.(interf_reg_reg)
          g.(interf_reg_mreg)
          g.(pref_reg_reg)
          (SetRegMreg.add (x, y) g.(pref_reg_mreg)).

(** [interfere x y g] holds iff there is a conflict edge in [g]
  between the two pseudo-registers [x] and [y]. *)

Definition interfere (x y: reg) (g: graph) : Prop :=
  SetRegReg.In (ordered_pair x y) g.(interf_reg_reg).

(** [interfere_mreg x y g] holds iff there is a conflict edge in [g]
  between the pseudo-register [x] and the machine register [y]. *)

Definition interfere_mreg (x: reg) (y: mreg) (g: graph) : Prop :=
  SetRegMreg.In (x, y) g.(interf_reg_mreg).

Lemma ordered_pair_charact:
  forall x y,
  ordered_pair x y = (x, y) \/ ordered_pair x y = (y, x).
Proof.
  unfold ordered_pair; intros.
  case (plt x y); intro; tauto.
Qed.

Lemma ordered_pair_sym:
  forall x y, ordered_pair y x = ordered_pair x y.
Proof.
  unfold ordered_pair; intros.
  case (plt x y); intro.
  case (plt y x); intro.
  unfold Plt in *; omegaContradiction.
  auto.
  case (plt y x); intro.
  auto.
  assert (Zpos x = Zpos y).  unfold Plt in *. omega.
  congruence.
Qed.

Lemma interfere_sym:
  forall x y g, interfere x y g -> interfere y x g.
Proof.
  unfold interfere; intros.
  rewrite ordered_pair_sym. auto.
Qed.

(** [graph_incl g1 g2] holds if [g2] contains all the conflict edges of [g1]
  and possibly more. *)

Definition graph_incl (g1 g2: graph) : Prop :=
  (forall x y, interfere x y g1 -> interfere x y g2) /\
  (forall x y, interfere_mreg x y g1 -> interfere_mreg x y g2).

Lemma graph_incl_trans:
  forall g1 g2 g3, graph_incl g1 g2 -> graph_incl g2 g3 -> graph_incl g1 g3.
Proof.
  unfold graph_incl; intros. 
  elim H0; elim H; intros.
  split; eauto.
Qed.

(** We show that the [add_] functions correctly record the desired
  conflicts, and preserve whatever conflict edges were already present. *)

Lemma add_interf_correct:
  forall x y g,
  interfere x y (add_interf x y g).
Proof.
  intros. unfold interfere, add_interf; simpl.
  apply SetRegReg.add_1. red. apply OrderedRegReg.eq_refl.
Qed.

Lemma add_interf_incl:
  forall a b g,  graph_incl g (add_interf a b g).
Proof.
  intros. split; intros.
  unfold add_interf, interfere; simpl.
  apply SetRegReg.add_2. exact H.
  exact H.
Qed.

Lemma add_interf_mreg_correct:
  forall x y g,
  interfere_mreg x y (add_interf_mreg x y g).
Proof.
  intros. unfold interfere_mreg, add_interf_mreg; simpl.
  apply SetRegMreg.add_1. red. apply OrderedRegMreg.eq_refl.
Qed.

Lemma add_interf_mreg_incl:
  forall a b g,  graph_incl g (add_interf_mreg a b g).
Proof.
  intros. split; intros.
  exact H.
  unfold add_interf_mreg, interfere_mreg; simpl.
  apply SetRegMreg.add_2. exact H.
Qed.

Lemma add_pref_incl:
  forall a b g,  graph_incl g (add_pref a b g).
Proof.
  intros. split; intros.
  exact H.
  exact H.
Qed.

Lemma add_pref_mreg_incl:
  forall a b g,  graph_incl g (add_pref_mreg a b g).
Proof.
  intros. split; intros.
  exact H.
  exact H.
Qed.

(** [all_interf_regs g] returns the set of pseudo-registers that
  are nodes of [g]. *)

Definition all_interf_regs (g: graph) : Regset.t :=
  SetRegReg.fold
    (fun r1r2 u => Regset.add (fst r1r2) (Regset.add (snd r1r2) u))
    g.(interf_reg_reg)
    (SetRegMreg.fold
      (fun r1m2 u => Regset.add (fst r1m2) u)
      g.(interf_reg_mreg)
      Regset.empty).

Lemma mem_add_tail:
  forall r r' u,
  Regset.mem r u = true -> Regset.mem r (Regset.add r' u) = true.
Proof.
  intros. case (Reg.eq r r'); intro.
  subst r'. apply Regset.mem_add_same.
  rewrite Regset.mem_add_other; auto.
Qed.

Lemma all_interf_regs_correct_aux_1:
  forall l u r,
  Regset.mem r u = true ->
  Regset.mem r
    (List.fold_right
      (fun r1r2 u => Regset.add (fst r1r2) (Regset.add (snd r1r2) u))
      u l) = true.
Proof.
  induction l; simpl; intros.
  auto.
  apply mem_add_tail. apply mem_add_tail. auto.
Qed.

Lemma all_interf_regs_correct_aux_2:
  forall l u r1 r2,
  InList OrderedRegReg.eq (r1, r2) l ->
  let u' :=
    List.fold_right
      (fun r1r2 u => Regset.add (fst r1r2) (Regset.add (snd r1r2) u))
      u l in
  Regset.mem r1 u' = true /\ Regset.mem r2 u' = true.
Proof.
  induction l; simpl; intros.
  inversion H.
  inversion H. elim H1. simpl. unfold OrderedReg.eq. 
  intros; subst r1; subst r2.
  split. apply Regset.mem_add_same. 
  apply mem_add_tail. apply Regset.mem_add_same.
  generalize (IHl u r1 r2 H1). intros [A B].
  split; repeat rewrite mem_add_tail; auto.
Qed.

Lemma all_interf_regs_correct_aux_3:
  forall l u r1 r2,
  InList OrderedRegMreg.eq (r1, r2) l ->
  let u' :=
    List.fold_right
      (fun r1r2 u => Regset.add (fst r1r2) u)
      u l in
  Regset.mem r1 u' = true.
Proof.
  induction l; simpl; intros.
  inversion H.
  inversion H. elim H1. simpl. unfold OrderedReg.eq. 
  intros; subst r1.
  apply Regset.mem_add_same. 
  apply mem_add_tail. apply IHl with r2. auto.
Qed.

Lemma all_interf_regs_correct_1:
  forall r1 r2 g,
  SetRegReg.In (r1, r2) g.(interf_reg_reg) ->
  Regset.mem r1 (all_interf_regs g) = true /\
  Regset.mem r2 (all_interf_regs g) = true.
Proof.
  intros. unfold all_interf_regs. 
  generalize (SetRegReg.fold_1
    g.(interf_reg_reg)
    (SetRegMreg.fold
        (fun (r1m2 : SetDepRegMreg.elt) (u : Regset.t) =>
         Regset.add (fst r1m2) u) (interf_reg_mreg g) Regset.empty)
    (fun (r1r2 : SetDepRegReg.elt) (u : Regset.t) =>
      Regset.add (fst r1r2) (Regset.add (snd r1r2) u))).
  intros [l [UN [INEQ EQ]]].
  rewrite EQ. apply all_interf_regs_correct_aux_2.
  elim (INEQ (r1, r2)); intros. auto.
Qed.

Lemma all_interf_regs_correct_2:
  forall r1 mr2 g,
  SetRegMreg.In (r1, mr2) g.(interf_reg_mreg) ->
  Regset.mem r1 (all_interf_regs g) = true.
Proof.
  intros. unfold all_interf_regs.
  generalize (SetRegReg.fold_1
    g.(interf_reg_reg)
    (SetRegMreg.fold
        (fun (r1m2 : SetDepRegMreg.elt) (u : Regset.t) =>
         Regset.add (fst r1m2) u) (interf_reg_mreg g) Regset.empty)
    (fun (r1r2 : SetDepRegReg.elt) (u : Regset.t) =>
      Regset.add (fst r1r2) (Regset.add (snd r1r2) u))).
  intros [l [UN [INEQ EQ]]].
  rewrite EQ. apply all_interf_regs_correct_aux_1.
  generalize (SetRegMreg.fold_1
    g.(interf_reg_mreg)
    Regset.empty
    (fun (r1r2 : SetDepRegMreg.elt) (u : Regset.t) =>
      Regset.add (fst r1r2) u)).
  change (PTree.t unit) with Regset.t.
  intros [l' [UN' [INEQ' EQ']]].
  rewrite EQ'. apply all_interf_regs_correct_aux_3 with mr2.
  elim (INEQ' (r1, mr2)); intros. auto.
Qed.

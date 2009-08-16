(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Solvers for dataflow inequations. *)

Require Import Coqlib.
Require Import Iteration.
Require Import Maps.
Require Import Lattice.

(** A forward dataflow problem is a set of inequations of the form
- [X(s) >= transf n X(n)] 
  if program point [s] is a successor of program point [n]
- [X(n) >= a]
  if [(n, a)] belongs to a given list of (program points, approximations).

The unknowns are the [X(n)], indexed by program points (e.g. nodes in the
CFG graph of a RTL function).  They range over a given ordered set that 
represents static approximations of the program state at each point.
The [transf] function is the abstract transfer function: it computes an 
approximation [transf n X(n)] of the program state after executing instruction
at point [n], as a function of the approximation [X(n)] of the program state
before executing that instruction.

Symmetrically, a backward dataflow problem is a set of inequations of the form
- [X(n) >= transf s X(s)] 
  if program point [s] is a successor of program point [n]
- [X(n) >= a]
  if [(n, a)] belongs to a given list of (program points, approximations).

The only difference with a forward dataflow problem is that the transfer
function [transf] now computes the approximation before a program point [s]
from the approximation [X(s)] after point [s].

This file defines three solvers for dataflow problems.  The first two
solve (optimally) forward and backward problems using Kildall's worklist
algorithm.  They assume that the unknowns range over a semi-lattice, that is,
an ordered type equipped with a least upper bound operation.

The last solver corresponds to propagation over extended basic blocks:
it returns approximate solutions of forward problems where the unknowns
range over any ordered type having a greatest element [top].  It simply
sets [X(n) = top] for all merge points [n], that is, program points having
several predecessors.  This solver is useful when least upper bounds of
approximations do not exist or are too expensive to compute. *)

(** * Solving forward dataflow problems using Kildall's algorithm *)

Definition successors_list (successors: PTree.t (list positive)) (pc: positive) : list positive :=
  match successors!pc with None => nil | Some l => l end.

Notation "a !!! b" := (successors_list a b) (at level 1).

(** A forward dataflow solver has the following generic interface.
  Unknowns range over the type [L.t], which is equipped with
  semi-lattice operations (see file [Lattice]).  *)

Module Type DATAFLOW_SOLVER.

  Declare Module L: SEMILATTICE.

  Variable fixpoint:
    forall (successors: PTree.t (list positive))
           (transf: positive -> L.t -> L.t)
           (entrypoints: list (positive * L.t)),
    option (PMap.t L.t).

  (** [fixpoint successors transf entrypoints] is the solver.
    It returns either an error or a mapping from program points to
    values of type [L.t] representing the solution.  [successors]
    is a finite map returning the list of successors of the given program
    point. [transf] is the transfer function, and [entrypoints] the additional
    constraints imposed on the solution. *)

  Hypothesis fixpoint_solution:
    forall successors transf entrypoints res n s,
    fixpoint successors transf entrypoints = Some res ->
    In s successors!!!n ->
    L.ge res!!s (transf n res!!n).

  (** The [fixpoint_solution] theorem shows that the returned solution,
    if any, satisfies the dataflow inequations. *)

  Hypothesis fixpoint_entry:
    forall successors transf entrypoints res n v,
    fixpoint successors transf entrypoints = Some res ->
    In (n, v) entrypoints ->
    L.ge res!!n v.

  (** The [fixpoint_entry] theorem shows that the returned solution,
    if any, satisfies the additional constraints expressed 
    by [entrypoints]. *)

  Hypothesis fixpoint_invariant:
    forall successors transf entrypoints 
           (P: L.t -> Prop),
    P L.bot ->
    (forall x y, P x -> P y -> P (L.lub x y)) ->
    (forall pc x, P x -> P (transf pc x)) ->
    (forall n v, In (n, v) entrypoints -> P v) ->
    forall res pc,
    fixpoint successors transf entrypoints = Some res ->
    P res!!pc.

  (** Finally, any property that is preserved by [L.lub] and [transf]
      and that holds for [L.bot] also holds for the results of
      the analysis. *)

End DATAFLOW_SOLVER.

(** Kildall's algorithm manipulates worklists, which are sets of CFG nodes
  equipped with a ``pick next node to examine'' operation.
  The algorithm converges faster if the nodes are chosen in an order
  consistent with a reverse postorder traversal of the CFG.
  For now, we parameterize the dataflow solver over a module
  that implements sets of CFG nodes. *)

Module Type NODE_SET.

  Variable t: Type.
  Variable add: positive -> t -> t.
  Variable pick: t -> option (positive * t).
  Variable initial: PTree.t (list positive) -> t.

  Variable In: positive -> t -> Prop.
  Hypothesis add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Hypothesis pick_none:
    forall s n, pick s = None -> ~In n s.
  Hypothesis pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Hypothesis initial_spec:
    forall successors n s,
    successors!n = Some s -> In n (initial successors).

End NODE_SET.

(** We now define a generic solver that works over 
    any semi-lattice structure. *)

Module Dataflow_Solver (LAT: SEMILATTICE) (NS: NODE_SET):
                          DATAFLOW_SOLVER with Module L := LAT.

Module L := LAT.

Section Kildall.

Variable successors: PTree.t (list positive).
Variable transf: positive -> L.t -> L.t.
Variable entrypoints: list (positive * L.t).

(** The state of the iteration has two components:
- A mapping from program points to values of type [L.t] representing
  the candidate solution found so far.
- A worklist of program points that remain to be considered.
*)

Record state : Type :=
  mkstate { st_in: PMap.t L.t; st_wrk: NS.t }.

(** Kildall's algorithm, in pseudo-code, is as follows:
<<
    while st_wrk is not empty, do
        extract a node n from st_wrk
        compute out = transf n st_in[n]
        for each successor s of n:
            compute in = lub st_in[s] out
            if in <> st_in[s]:
                st_in[s] := in
                st_wrk := st_wrk union {s}
            end if
        end for
    end while
    return st_in
>>

The initial state is built as follows:
- The initial mapping sets all program points to [L.bot], except
  those mentioned in the [entrypoints] list, for which we take
  the associated approximation as initial value.  Since a program
  point can be mentioned several times in [entrypoints], with different
  approximations, we actually take the l.u.b. of these approximations.
- The initial worklist contains all the program points. *)

Fixpoint start_state_in (ep: list (positive * L.t)) : PMap.t L.t :=
  match ep with
  | nil =>
      PMap.init L.bot
  | (n, v) :: rem =>
      let m := start_state_in rem in PMap.set n (L.lub m!!n v) m
  end.

Definition start_state :=
  mkstate (start_state_in entrypoints) (NS.initial successors).

(** [propagate_succ] corresponds, in the pseudocode,
  to the body of the [for] loop iterating over all successors. *)

Definition propagate_succ (s: state) (out: L.t) (n: positive) :=
  let oldl := s.(st_in)!!n in
  let newl := L.lub oldl out in
  if L.beq oldl newl
  then s
  else mkstate (PMap.set n newl s.(st_in)) (NS.add n s.(st_wrk)).

(** [propagate_succ_list] corresponds, in the pseudocode,
  to the [for] loop iterating over all successors. *)

Fixpoint propagate_succ_list (s: state) (out: L.t) (succs: list positive)
                             {struct succs} : state :=
  match succs with
  | nil => s
  | n :: rem => propagate_succ_list (propagate_succ s out n) out rem
  end.

(** [step] corresponds to the body of the outer [while] loop in the
  pseudocode. *)

Definition step (s: state) : PMap.t L.t + state :=
  match NS.pick s.(st_wrk) with
  | None => 
      inl _ s.(st_in)
  | Some(n, rem) =>
      inr _ (propagate_succ_list
              (mkstate s.(st_in) rem)
              (transf n s.(st_in)!!n)
              (successors!!!n))
  end.

(** The whole fixpoint computation is the iteration of [step] from
  the start state. *)

Definition fixpoint : option (PMap.t L.t) :=
  PrimIter.iterate _ _ step start_state.

(** ** Monotonicity properties *)

(** We first show that the [st_in] part of the state evolves monotonically:
  at each step, the values of the [st_in[n]] either remain the same or
  increase with respect to the [L.ge] ordering. *)

Definition in_incr (in1 in2: PMap.t L.t) : Prop :=
  forall n, L.ge in2!!n in1!!n.

Lemma in_incr_refl:
  forall in1, in_incr in1 in1.
Proof.
  unfold in_incr; intros. apply L.ge_refl. apply L.eq_refl.
Qed.

Lemma in_incr_trans:
  forall in1 in2 in3, in_incr in1 in2 -> in_incr in2 in3 -> in_incr in1 in3.
Proof.
  unfold in_incr; intros. apply L.ge_trans with in2!!n; auto.
Qed.

Lemma propagate_succ_incr:
  forall st out n,
  in_incr st.(st_in) (propagate_succ st out n).(st_in).
Proof.
  unfold in_incr, propagate_succ; simpl; intros.
  case (L.beq st.(st_in)!!n (L.lub st.(st_in)!!n out)).
  apply L.ge_refl. apply L.eq_refl.
  simpl. case (peq n n0); intro.
  subst n0. rewrite PMap.gss. apply L.ge_lub_left.
  rewrite PMap.gso; auto. apply L.ge_refl. apply L.eq_refl.
Qed.

Lemma propagate_succ_list_incr:
  forall out scs st,
  in_incr st.(st_in) (propagate_succ_list st out scs).(st_in).
Proof.
  induction scs; simpl; intros.
  apply in_incr_refl.
  apply in_incr_trans with (propagate_succ st out a).(st_in). 
  apply propagate_succ_incr. auto.
Qed. 

Lemma fixpoint_incr:
  forall res,
  fixpoint = Some res -> in_incr (start_state_in entrypoints) res.
Proof.
  unfold fixpoint; intros.
  change (start_state_in entrypoints) with start_state.(st_in).
  eapply (PrimIter.iterate_prop _ _ step
    (fun st => in_incr start_state.(st_in) st.(st_in))
    (fun res => in_incr start_state.(st_in) res)).

  intros st INCR. unfold step.
  destruct (NS.pick st.(st_wrk)) as [ [n rem] | ].
  apply in_incr_trans with st.(st_in). auto. 
  change st.(st_in) with (mkstate st.(st_in) rem).(st_in). 
  apply propagate_succ_list_incr. 
  auto. 

  eauto. apply in_incr_refl.
Qed.

(** ** Correctness invariant *)

(** The following invariant is preserved at each iteration of Kildall's
  algorithm: for all program points [n], either
  [n] is in the worklist, or the inequations associated with [n]
  ([st_in[s] >= transf n st_in[n]] for all successors [s] of [n])
  hold.  In other terms, the worklist contains all nodes that do not
  yet satisfy their inequations. *)

Definition good_state (st: state) : Prop :=
  forall n,
  NS.In n st.(st_wrk) \/
  (forall s, In s (successors!!!n) ->
             L.ge st.(st_in)!!s (transf n st.(st_in)!!n)).

(** We show that the start state satisfies the invariant, and that
  the [step] function preserves it. *)

Lemma start_state_good:
  good_state start_state.
Proof.
  unfold good_state, start_state; intros.
  case_eq (successors!n); intros.
  left; simpl. eapply NS.initial_spec. eauto.
  unfold successors_list. rewrite H. right; intros. contradiction.
Qed.

Lemma propagate_succ_charact:
  forall st out n,
  let st' := propagate_succ st out n in
  L.ge st'.(st_in)!!n out /\
  (forall s, n <> s -> st'.(st_in)!!s = st.(st_in)!!s).
Proof.
  unfold propagate_succ; intros; simpl.
  predSpec L.beq L.beq_correct
           ((st_in st) !! n) (L.lub (st_in st) !! n out).
  split.
  eapply L.ge_trans. apply L.ge_refl. apply H; auto.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl. 
  apply L.ge_lub_left. 
  auto.

  simpl. split.
  rewrite PMap.gss.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl. 
  apply L.ge_lub_left. 
  intros. rewrite PMap.gso; auto.
Qed.

Lemma propagate_succ_list_charact:
  forall out scs st,
  let st' := propagate_succ_list st out scs in
  forall s,
  (In s scs -> L.ge st'.(st_in)!!s out) /\
  (~(In s scs) -> st'.(st_in)!!s = st.(st_in)!!s).
Proof.
  induction scs; simpl; intros.
  tauto.
  generalize (IHscs (propagate_succ st out a) s). intros [A B].
  generalize (propagate_succ_charact st out a). intros [C D].
  split; intros.
  elim H; intro.
  subst s.
  apply L.ge_trans with (propagate_succ st out a).(st_in)!!a.
  apply propagate_succ_list_incr. assumption.
  apply A. auto.
  transitivity (propagate_succ st out a).(st_in)!!s.
  apply B. tauto.
  apply D. tauto.
Qed.

Lemma propagate_succ_incr_worklist:
  forall st out n x,
  NS.In x st.(st_wrk) -> NS.In x (propagate_succ st out n).(st_wrk).
Proof.
  intros. unfold propagate_succ. 
  case (L.beq (st_in st) !! n (L.lub (st_in st) !! n out)).
  auto.
  simpl. rewrite NS.add_spec. auto.
Qed.

Lemma propagate_succ_list_incr_worklist:
  forall out scs st x,
  NS.In x st.(st_wrk) -> NS.In x (propagate_succ_list st out scs).(st_wrk).
Proof.
  induction scs; simpl; intros.
  auto.
  apply IHscs. apply propagate_succ_incr_worklist. auto.
Qed.

Lemma propagate_succ_records_changes:
  forall st out n s,
  let st' := propagate_succ st out n in
  NS.In s st'.(st_wrk) \/ st'.(st_in)!!s = st.(st_in)!!s.
Proof.
  simpl. intros. unfold propagate_succ. 
  case (L.beq (st_in st) !! n (L.lub (st_in st) !! n out)).
  right; auto.
  case (peq s n); intro.
  subst s. left. simpl. rewrite NS.add_spec. auto.
  right. simpl. apply PMap.gso. auto.
Qed.

Lemma propagate_succ_list_records_changes:
  forall out scs st s,
  let st' := propagate_succ_list st out scs in
  NS.In s st'.(st_wrk) \/ st'.(st_in)!!s = st.(st_in)!!s.
Proof.
  induction scs; simpl; intros.
  right; auto.
  elim (propagate_succ_records_changes st out a s); intro.
  left. apply propagate_succ_list_incr_worklist. auto.
  rewrite <- H. auto.
Qed.

Lemma step_state_good:
  forall st n rem,
  NS.pick st.(st_wrk) = Some(n, rem) ->
  good_state st ->
  good_state (propagate_succ_list (mkstate st.(st_in) rem)
                                  (transf n st.(st_in)!!n)
                                  (successors!!!n)).
Proof.
  unfold good_state. intros st n rem WKL GOOD x.
  generalize (NS.pick_some _ _ _ WKL); intro PICK.
  set (out := transf n st.(st_in)!!n).
  elim (propagate_succ_list_records_changes 
          out (successors!!!n) (mkstate st.(st_in) rem) x).
  intro; left; auto.
  simpl; intros EQ. rewrite EQ.
  (* Case 1: x = n *)
  case (peq x n); intro.
  subst x.
  right; intros.
  elim (propagate_succ_list_charact out (successors!!!n)
          (mkstate st.(st_in) rem) s); intros.
  auto.
  (* Case 2: x <> n *)
  elim (GOOD x); intro.
  (* Case 2.1: x was already in worklist, still is *)
  left. apply propagate_succ_list_incr_worklist.
  simpl. rewrite PICK in H. elim H; intro. congruence. auto.
  (* Case 2.2: x was not in worklist *)
  right; intros.
  case (In_dec peq s (successors!!!n)); intro.
  (* Case 2.2.1: s is a successor of n, it may have increased *)
  apply L.ge_trans with st.(st_in)!!s.
  change st.(st_in)!!s with (mkstate st.(st_in) rem).(st_in)!!s.
  apply propagate_succ_list_incr. 
  auto.
  (* Case 2.2.2: s is not a successor of n, it did not change *)
  elim (propagate_succ_list_charact out (successors!!!n)
          (mkstate st.(st_in) rem) s); intros.
  rewrite H2. simpl. auto. auto.
Qed.

(** ** Correctness of the solution returned by [iterate]. *)

(** As a consequence of the [good_state] invariant, the result of
  [fixpoint], if defined, is a solution of the dataflow inequations,
  since [st_wrk] is empty when the iteration terminates. *)

Theorem fixpoint_solution:
  forall res n s,
  fixpoint = Some res ->
  In s (successors!!!n) ->
  L.ge res!!s (transf n res!!n).
Proof.
  assert (forall res, fixpoint = Some res ->
          forall n s,
          In s successors!!!n ->
          L.ge res!!s (transf n res!!n)).
  unfold fixpoint. intros res PI. pattern res. 
  eapply (PrimIter.iterate_prop _ _ step good_state).

  intros st GOOD. unfold step. 
  caseEq (NS.pick st.(st_wrk)). 
  intros [n rem] PICK. apply step_state_good; auto. 
  intros. 
  elim (GOOD n); intro. 
  elim (NS.pick_none _ n H). auto.
  auto.

  eauto. apply start_state_good. eauto.
Qed.

(** As a consequence of the monotonicity property, the result of
  [fixpoint], if defined, is pointwise greater than or equal the
  initial mapping.  Therefore, it satisfies the additional constraints
  stated in [entrypoints]. *)

Lemma start_state_in_entry:
  forall ep n v,
  In (n, v) ep ->
  L.ge (start_state_in ep)!!n v.
Proof.
  induction ep; simpl; intros.
  elim H.
  elim H; intros.
  subst a. rewrite PMap.gss.
  eapply L.ge_compat. apply L.lub_commut. apply L.eq_refl. 
  apply L.ge_lub_left.
  destruct a. rewrite PMap.gsspec. case (peq n p); intro.
  subst p. apply L.ge_trans with (start_state_in ep)!!n.
  apply L.ge_lub_left. auto.
  auto.
Qed.

Theorem fixpoint_entry:
  forall res n v,
  fixpoint = Some res ->
  In (n, v) entrypoints ->
  L.ge res!!n v.
Proof.
  intros.
  apply L.ge_trans with (start_state_in entrypoints)!!n.
  apply fixpoint_incr. auto.
  apply start_state_in_entry. auto.
Qed.

(** ** Preservation of a property over solutions *)

Variable P: L.t -> Prop.
Hypothesis P_bot: P L.bot.
Hypothesis P_lub: forall x y, P x -> P y -> P (L.lub x y).
Hypothesis P_transf: forall pc x, P x -> P (transf pc x).
Hypothesis P_entrypoints: forall n v, In (n, v) entrypoints -> P v.

Theorem fixpoint_invariant:
  forall res pc,
  fixpoint = Some res ->
  P res!!pc.
Proof.
  assert (forall ep,
          (forall n v, In (n, v) ep -> P v) ->
          forall pc, P (start_state_in ep)!!pc).
    induction ep; intros; simpl.
    rewrite PMap.gi. auto.
    simpl in H.
    assert (P (start_state_in ep)!!pc). apply IHep. eauto.  
    destruct a as [n v]. rewrite PMap.gsspec. destruct (peq pc n).
    apply P_lub. subst. auto. eapply H. left; reflexivity. auto.
  set (inv := fun st => forall pc, P (st.(st_in)!!pc)).
  assert (forall st v n, inv st -> P v -> inv (propagate_succ st v n)).
    unfold inv, propagate_succ. intros. 
    destruct (LAT.beq (st_in st)!!n (LAT.lub (st_in st)!!n v)).
    auto. simpl. rewrite PMap.gsspec. destruct (peq pc n). 
    apply P_lub. subst n; auto. auto.
    auto.
  assert (forall l st v, inv st -> P v -> inv (propagate_succ_list st v l)).
    induction l; intros; simpl. auto.
    apply IHl; auto.
  assert (forall res, fixpoint = Some res -> forall pc, P res!!pc).
    unfold fixpoint. intros res0 RES0. pattern res0.
    eapply (PrimIter.iterate_prop _ _ step inv).
    intros. unfold step. destruct (NS.pick (st_wrk a)) as [[n rem] | ].
    apply H1. auto. apply P_transf. apply H2.
    assumption.
    eauto. 
    unfold inv, start_state; simpl. auto. 
  intros. auto.
Qed.

End Kildall.

End Dataflow_Solver.

(** * Solving backward dataflow problems using Kildall's algorithm *)

(** A backward dataflow problem on a given flow graph is a forward
  dataflow program on the reversed flow graph, where predecessors replace
  successors.  We exploit this observation to cheaply derive a backward
  solver from the forward solver. *)

(** ** Construction of the predecessor relation *)

Section Predecessor.

Variable successors: PTree.t (list positive).

Fixpoint add_successors (pred: PTree.t (list positive))
                        (from: positive) (tolist: list positive)
                        {struct tolist} : PTree.t (list positive) :=
  match tolist with
  | nil => pred
  | to :: rem => add_successors (PTree.set to (from :: pred!!!to) pred) from rem
  end.

Lemma add_successors_correct:
  forall tolist from pred n s,
  In n pred!!!s \/ (n = from /\ In s tolist) -> 
  In n (add_successors pred from tolist)!!!s.
Proof.
  induction tolist; simpl; intros.
  tauto.
  apply IHtolist.
  unfold successors_list at 1. rewrite PTree.gsspec. destruct (peq s a).
  subst a. destruct H. auto with coqlib. 
  destruct H. subst n. auto with coqlib. 
  fold (successors_list pred s). intuition congruence.
Qed.

Definition make_predecessors : PTree.t (list positive) :=
  PTree.fold add_successors successors (PTree.empty (list positive)).

Lemma make_predecessors_correct:
  forall n s,
  In s successors!!!n ->
  In n make_predecessors!!!s.
Proof.
  set (P := fun succ pred =>
          forall n s, In s succ!!!n -> In n pred!!!s).
  unfold make_predecessors.
  apply PTree_Properties.fold_rec with (P := P).
(* extensionality *)
  unfold P; unfold successors_list; intros.
  rewrite <- H in H1. auto.
(* base case *)
  red; unfold successors_list. intros n s. repeat rewrite PTree.gempty. auto.
(* inductive case *)
  unfold P; intros. apply add_successors_correct.
  unfold successors_list in H2. rewrite PTree.gsspec in H2. 
  destruct (peq n k).
  subst k. auto.
  fold (successors_list m n) in H2. auto.
Qed.

End Predecessor.

(** ** Solving backward dataflow problems *)

(** The interface to a backward dataflow solver is as follows. *)

Module Type BACKWARD_DATAFLOW_SOLVER.

  Declare Module L: SEMILATTICE.

  Variable fixpoint:
    PTree.t (list positive) ->
    (positive -> L.t -> L.t) ->
    list (positive * L.t) ->
    option (PMap.t L.t).

  Hypothesis fixpoint_solution:
    forall successors transf entrypoints res n s,
    fixpoint successors transf entrypoints = Some res ->
    In s (successors!!!n) ->
    L.ge res!!n (transf s res!!s).

  Hypothesis fixpoint_entry:
    forall successors transf entrypoints res n v,
    fixpoint successors transf entrypoints = Some res ->
    In (n, v) entrypoints ->
    L.ge res!!n v.

  Hypothesis fixpoint_invariant:
    forall successors transf entrypoints (P: L.t -> Prop),
    P L.bot ->
    (forall x y, P x -> P y -> P (L.lub x y)) ->
    (forall pc x, P x -> P (transf pc x)) ->
    (forall n v, In (n, v) entrypoints -> P v) ->
    forall res pc,
    fixpoint successors transf entrypoints = Some res ->
    P res!!pc.

End BACKWARD_DATAFLOW_SOLVER.

(** We construct a generic backward dataflow solver, working over any
  semi-lattice structure, by applying the forward dataflow solver
  with the predecessor relation instead of the successor relation. *)

Module Backward_Dataflow_Solver (LAT: SEMILATTICE) (NS: NODE_SET):
                   BACKWARD_DATAFLOW_SOLVER with Module L := LAT.

Module L := LAT.

Module DS := Dataflow_Solver L NS.

Section Kildall.

Variable successors: PTree.t (list positive).
Variable transf: positive -> L.t -> L.t.
Variable entrypoints: list (positive * L.t).

Definition fixpoint :=
  DS.fixpoint (make_predecessors successors) transf entrypoints.

Theorem fixpoint_solution:
  forall res n s,
  fixpoint = Some res ->
  In s (successors!!!n) ->
  L.ge res!!n (transf s res!!s).
Proof.
  intros. apply DS.fixpoint_solution with
    (make_predecessors successors) entrypoints.
  exact H.
  apply make_predecessors_correct; auto.
Qed.

Theorem fixpoint_entry:
  forall res n v,
  fixpoint = Some res ->
  In (n, v) entrypoints ->
  L.ge res!!n v.
Proof.
  intros. apply DS.fixpoint_entry with
    (make_predecessors successors) transf entrypoints.
  exact H. auto.
Qed.

Theorem fixpoint_invariant:
  forall (P: L.t -> Prop),
  P L.bot ->
  (forall x y, P x -> P y -> P (L.lub x y)) ->
  (forall pc x, P x -> P (transf pc x)) ->
  (forall n v, In (n, v) entrypoints -> P v) ->
  forall res pc,
  fixpoint = Some res ->
  P res!!pc.
Proof.
  intros. apply DS.fixpoint_invariant with 
    (make_predecessors successors) transf entrypoints; auto. 
Qed.

End Kildall.

End Backward_Dataflow_Solver.

(** * Analysis on extended basic blocks *)

(** We now define an approximate solver for forward dataflow problems
  that proceeds by forward propagation over extended basic blocks.
  In other terms, program points with multiple predecessors are mapped
  to [L.top] (the greatest, or coarsest, approximation) and the other
  program points are mapped to [transf p X[p]] where [p] is their unique
  predecessor. 

  This analysis applies to any type of approximations equipped with
  an ordering and a greatest element. *)

Module Type ORDERED_TYPE_WITH_TOP.

  Variable t: Type.
  Variable ge: t -> t -> Prop.
  Variable top: t.
  Hypothesis top_ge: forall x, ge top x.
  Hypothesis refl_ge: forall x, ge x x.

End ORDERED_TYPE_WITH_TOP.

(** The interface of the solver is similar to that of Kildall's forward
  solver.  We provide one additional theorem [fixpoint_invariant]
  stating that any property preserved by the [transf] function 
  holds for the returned solution. *)

Module Type BBLOCK_SOLVER.

  Declare Module L: ORDERED_TYPE_WITH_TOP.

  Variable fixpoint:
    PTree.t (list positive) ->
    (positive -> L.t -> L.t) ->
    positive ->
    option (PMap.t L.t).

  Hypothesis fixpoint_solution:
    forall successors transf entrypoint res n s,
    fixpoint successors transf entrypoint = Some res ->
    In s (successors!!!n) ->
    L.ge res!!s (transf n res!!n).

  Hypothesis fixpoint_entry:
    forall successors transf entrypoint res,
    fixpoint successors transf entrypoint = Some res ->
    res!!entrypoint = L.top.

  Hypothesis fixpoint_invariant:
    forall successors transf entrypoint 
           (P: L.t -> Prop),
    P L.top ->
    (forall pc x, P x -> P (transf pc x)) ->
    forall res pc,
    fixpoint successors transf entrypoint = Some res ->
    P res!!pc.

End BBLOCK_SOLVER.

(** The implementation of the ``extended basic block'' solver is a
  functor parameterized by any ordered type with a top element. *)

Module BBlock_solver(LAT: ORDERED_TYPE_WITH_TOP):
                        BBLOCK_SOLVER with Module L := LAT.

Module L := LAT.

Section Solver.

Variable successors: PTree.t (list positive).
Variable transf: positive -> L.t -> L.t.
Variable entrypoint: positive.
Variable P: L.t -> Prop.
Hypothesis Ptop: P L.top.
Hypothesis Ptransf: forall pc x, P x -> P (transf pc x).

Definition bbmap := positive -> bool.
Definition result := PMap.t L.t.

(** As in Kildall's solver, the state of the iteration has two components:
- A mapping from program points to values of type [L.t] representing
  the candidate solution found so far.
- A worklist of program points that remain to be considered.
*)

Record state : Type := mkstate
  { st_in: result; st_wrk: list positive }.

(** The ``extended basic block'' algorithm, in pseudo-code, is as follows:
<<
    st_wrk := the set of all points n having multiple predecessors
    st_in  := the mapping n -> L.top

    while st_wrk is not empty, do
        extract a node n from st_wrk
        compute out = transf n st_in[n]
        for each successor s of n:
            if s has only one predecessor (namely, n):
                st_in[s] := out
                st_wrk := st_wrk union {s}
            end if
        end for
    end while
    return st_in
>>
**)

Fixpoint propagate_successors
    (bb: bbmap) (succs: list positive) (l: L.t) (st: state)
    {struct succs} : state :=
  match succs with
  | nil => st
  | s1 :: sl =>
      if bb s1 then
        propagate_successors bb sl l st
      else
        propagate_successors bb sl l
          (mkstate (PMap.set s1 l st.(st_in))
                   (s1 :: st.(st_wrk)))
  end.

Definition step (bb: bbmap) (st: state) : result + state :=
  match st.(st_wrk) with
  | nil => inl _ st.(st_in)
  | pc :: rem =>
        inr _ (propagate_successors 
                 bb (successors!!!pc)
                 (transf pc st.(st_in)!!pc)
                 (mkstate st.(st_in) rem))
  end.

(** Recognition of program points that have more than one predecessor. *)

Definition is_basic_block_head 
    (preds: PTree.t (list positive)) (pc: positive) : bool :=
  if peq pc entrypoint then true else
    match preds!!!pc with
    | nil => false
    | s :: nil => peq s pc
    | _ :: _ :: _ => true
    end.

Definition basic_block_map : bbmap :=
  is_basic_block_head (make_predecessors successors).

Definition basic_block_list (bb: bbmap) : list positive :=
  PTree.fold (fun l pc scs => if bb pc then pc :: l else l)
             successors nil.

(** The computation of the approximate solution. *)

Definition fixpoint : option result :=
  let bb := basic_block_map in
  PrimIter.iterate _ _ (step bb) (mkstate (PMap.init L.top) (basic_block_list bb)).

(** ** Properties of predecessors and multiple-predecessors nodes *)

Definition predecessors := make_predecessors successors.

Lemma predecessors_correct:
  forall n s,
  In s successors!!!n -> In n predecessors!!!s.
Proof.
  intros. unfold predecessors. eapply make_predecessors_correct; eauto.
Qed.

Lemma multiple_predecessors:
  forall s n1 n2,
  In s (successors!!!n1) ->
  In s (successors!!!n2) ->
  n1 <> n2 ->
  basic_block_map s = true.
Proof.
  intros. 
  assert (In n1 predecessors!!!s). apply predecessors_correct; auto.
  assert (In n2 predecessors!!!s). apply predecessors_correct; auto.
  unfold basic_block_map, is_basic_block_head.
  destruct (peq s entrypoint). auto. 
  fold predecessors.
  destruct (predecessors!!!s). 
  auto.
  destruct l.
  simpl in H2. simpl in H3. intuition congruence. 
  auto.
Qed.

Lemma no_self_loop:
  forall n,
  In n (successors!!!n) -> basic_block_map n = true.
Proof.
  intros. unfold basic_block_map, is_basic_block_head.
  destruct (peq n entrypoint). auto. 
  fold predecessors. 
  generalize (predecessors_correct n n H). intro.
  destruct (predecessors!!!n). auto.
  destruct l. replace n with p. apply peq_true. simpl in H0. tauto. 
  auto.
Qed.

(** ** Correctness invariant *)

(** The invariant over the state is as follows:
- Points with several predecessors are mapped to [L.top]
- Points not in the worklist satisfy their inequations 
  (as in Kildall's algorithm).
*)

Definition state_invariant (st: state) : Prop :=
  (forall n, basic_block_map n = true -> st.(st_in)!!n = L.top)
/\
  (forall n,
   In n st.(st_wrk) \/
   (forall s, In s (successors!!!n) -> 
               L.ge st.(st_in)!!s (transf n st.(st_in)!!n))).

Lemma propagate_successors_charact1:
  forall bb succs l st,
  incl st.(st_wrk)
       (propagate_successors bb succs l st).(st_wrk).
Proof.
  induction succs; simpl; intros.
  apply incl_refl.
  case (bb a).
  auto.
  apply incl_tran with (a :: st_wrk st).
  apply incl_tl. apply incl_refl.
  set (st1 := (mkstate (PMap.set a l (st_in st)) (a :: st_wrk st))).
  change (a :: st_wrk st) with (st_wrk st1).
  auto.
Qed.

Lemma propagate_successors_charact2:
  forall bb succs l st n,
  let st' := propagate_successors bb succs l st in
  (In n succs -> bb n = false -> In n st'.(st_wrk) /\ st'.(st_in)!!n = l)
/\ (~In n succs \/ bb n = true -> st'.(st_in)!!n = st.(st_in)!!n).
Proof.
  induction succs; simpl; intros.
  (* Base case *)
  split. tauto. auto.
  (* Inductive case *)
  caseEq (bb a); intro.
  elim (IHsuccs l st n); intros A B.
  split; intros. apply A; auto.
  elim H0; intro. subst a. congruence. auto. 
  apply B. tauto. 
  set (st1 := mkstate (PMap.set a l (st_in st)) (a :: st_wrk st)).
  elim (IHsuccs l st1 n); intros A B.
  split; intros.
  elim H0; intros.
  subst n. split.
  apply propagate_successors_charact1. simpl. tauto.
  case (In_dec peq a succs); intro.
  elim (A i H1); auto.
  rewrite B. unfold st1; simpl. apply PMap.gss. tauto.
  apply A; auto.
  rewrite B. unfold st1; simpl. apply PMap.gso. 
  red; intro; subst n. elim H0; intro. tauto. congruence.
  tauto. 
Qed.

Lemma propagate_successors_invariant:
  forall pc res rem,
  state_invariant (mkstate res (pc :: rem)) ->
  state_invariant 
    (propagate_successors basic_block_map (successors!!!pc)
                          (transf pc res!!pc)
                          (mkstate res rem)).
Proof.
  intros until rem. intros [INV1 INV2]. simpl in INV1. simpl in INV2.
  set (l := transf pc res!!pc).
  generalize (propagate_successors_charact1 basic_block_map
                (successors!!! pc) l (mkstate res rem)).
  generalize (propagate_successors_charact2 basic_block_map
                (successors!!!pc) l (mkstate res rem)).
  set (st1 := propagate_successors basic_block_map
                 (successors!!!pc) l (mkstate res rem)).
  intros A B. simpl in A. 
  (* First part: BB entries remain at top *)
  split; intros.
  elim (A n); intros C D. rewrite D. simpl. apply INV1. auto. tauto. 
  (* Second part: monotonicity *)
  (* Case 1: n = pc *)
  case (peq pc n); intros.
  subst n. right; intros. 
  elim (A s); intros C D.
  replace (st1.(st_in)!!pc) with res!!pc. fold l. 
  caseEq (basic_block_map s); intro.
  rewrite D. simpl. rewrite INV1. apply L.top_ge. auto. tauto. 
  elim (C H H0); intros. rewrite H2. apply L.refl_ge. 
  elim (A pc); intros E F. rewrite F. reflexivity. 
  case (In_dec peq pc (successors!!!pc)); intro.
  right. apply no_self_loop; auto. 
  left; auto.
  (* Case 2: n <> pc *)
  elim (INV2 n); intro.
  (* Case 2.1: n was already in worklist, still is *)
  left. apply B. simpl. tauto.
  (* Case 2.2: n was not in worklist *)
  assert (INV3: forall s, In s (successors!!!n) -> st1.(st_in)!!s = res!!s).
    (* Amazingly, successors of n do not change.  The only way
       they could change is if they were successors of pc as well,
       but that gives them two different predecessors, so
       they are basic block heads, and thus do not change! *)
    intros. elim (A s); intros C D. rewrite D. reflexivity. 
    case (In_dec peq s (successors!!!pc)); intro.
    right. apply multiple_predecessors with n pc; auto.
    left; auto.
  case (In_dec peq n (successors!!!pc)); intro.
  (* Case 2.2.1: n is a successor of pc. Either it is in the
     worklist or it did not change *)
  caseEq (basic_block_map n); intro.
  right; intros. 
  elim (A n); intros C D. rewrite D. rewrite INV3; auto.
  tauto.
  left. elim (A n); intros C D. elim (C i H0); intros. auto.
  (* Case 2.2.2: n is not a successor of pc. It did not change. *)
  right; intros.
  elim (A n); intros C D. rewrite D. 
  rewrite INV3; auto.
  tauto.
Qed.

Lemma initial_state_invariant:
  state_invariant (mkstate (PMap.init L.top) (basic_block_list basic_block_map)).
Proof.
  split; simpl; intros.
  apply PMap.gi.
  right. intros. repeat rewrite PMap.gi. apply L.top_ge.
Qed.

Lemma analyze_invariant:
  forall res,
  fixpoint = Some res ->
  state_invariant (mkstate res nil).
Proof.
  unfold fixpoint; intros. pattern res.
  eapply (PrimIter.iterate_prop _ _ (step basic_block_map)
           state_invariant).

  intros st INV. destruct st as [stin stwrk]. 
  unfold step. simpl. caseEq stwrk.
  intro. congruence.

  intros pc rem WRK. 
  apply propagate_successors_invariant; auto. congruence. 

  eauto. apply initial_state_invariant.
Qed.

(** ** Correctness of the returned solution *)

Theorem fixpoint_solution:
  forall res n s,
  fixpoint = Some res ->
  In s (successors!!!n) ->
  L.ge res!!s (transf n res!!n).
Proof.
  intros. 
  assert (state_invariant (mkstate res nil)).
  eapply analyze_invariant; eauto. 
  elim H1; simpl; intros. 
  elim (H3 n); intros. 
  contradiction.
  auto.
Qed.

Theorem fixpoint_entry:
  forall res,
  fixpoint = Some res ->
  res!!entrypoint = L.top.
Proof.
  intros. 
  assert (state_invariant (mkstate res nil)).
  eapply analyze_invariant; eauto. 
  elim H0; simpl; intros. 
  apply H1. unfold basic_block_map, is_basic_block_head.
  fold predecessors. apply peq_true. 
Qed. 

(** ** Preservation of a property over solutions *)

Definition Pstate (st: state) : Prop :=
  forall pc, P st.(st_in)!!pc.

Lemma propagate_successors_P:
  forall bb l,
  P l ->
  forall succs st,
  Pstate st ->
  Pstate (propagate_successors bb succs l st).
Proof.
  induction succs; simpl; intros.
  auto.
  case (bb a). auto. 
  apply IHsuccs. red; simpl; intros. 
  rewrite PMap.gsspec. case (peq pc a); intro.
  auto. apply H0.
Qed.

Theorem fixpoint_invariant:
  forall res pc, fixpoint = Some res -> P res!!pc.
Proof.
  unfold fixpoint; intros. pattern res. 
  eapply (PrimIter.iterate_prop _ _ (step basic_block_map) Pstate).

  intros st PS. unfold step. destruct (st.(st_wrk)).
  apply PS.
  assert (PS2: Pstate (mkstate st.(st_in) l)).
    red; intro; simpl. apply PS.
  apply propagate_successors_P. auto. auto. eauto. 

  red; intro; simpl. rewrite PMap.gi. apply Ptop.
Qed.

End Solver.

End BBlock_solver.

(** ** Node sets *)

(** We now define implementations of the [NODE_SET] interface
  appropriate for forward and backward dataflow analysis.
  As mentioned earlier, we aim for a traversal of the CFG nodes
  in reverse postorder (for forward analysis) or postorder
  (for backward analysis).  We take advantage of the following
  fact, valid for all CFG generated by translation from Cminor:
  the enumeration [n-1], [n-2], ..., 3, 2, 1 where [n] is the
  top CFG node is a reverse postorder traversal.
  Therefore, for forward analysis, we will use an implementation
  of [NODE_SET] where the [pick] operation selects the 
  greatest node in the working list.  For backward analysis,
  we will similarly pick the smallest node in the working list. *)

Require Import FSets.
Require Import FSetAVL.
Require Import Ordered.

Module PositiveSet := FSetAVL.Make(OrderedPositive).
Module PositiveSetFacts := FSetFacts.Facts(PositiveSet).

Module NodeSetForward <: NODE_SET.
  Definition t := PositiveSet.t.
  Definition add (n: positive) (s: t) : t := PositiveSet.add n s.
  Definition pick (s: t) :=
    match PositiveSet.max_elt s with
    | Some n => Some(n, PositiveSet.remove n s)
    | None => None
    end.
  Definition initial (successors: PTree.t (list positive)) :=
    PTree.fold (fun s pc scs => PositiveSet.add pc s) successors PositiveSet.empty.
  Definition In := PositiveSet.In.

  Lemma add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Proof.
    intros. exact (PositiveSetFacts.add_iff s n n').
  Qed.
    
  Lemma pick_none:
    forall s n, pick s = None -> ~In n s.
  Proof.
    intros until n; unfold pick. caseEq (PositiveSet.max_elt s); intros.
    congruence.
    apply PositiveSet.max_elt_3. auto.
  Qed.

  Lemma pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Proof.
    intros until s'; unfold pick. caseEq (PositiveSet.max_elt s); intros.
    inversion H0; clear H0; subst. 
    split; intros. 
    destruct (peq n n'). auto. right. apply PositiveSet.remove_2; assumption.
    elim H0; intro. subst n'. apply PositiveSet.max_elt_1. auto. 
    apply PositiveSet.remove_3 with n; assumption.
    congruence.
  Qed.

  Lemma initial_spec:
    forall successors n s, 
    successors!n = Some s -> In n (initial successors).
  Proof.
    intros successors.
    apply PTree_Properties.fold_rec with
      (P := fun succ set =>
              forall n s, succ!n = Some s -> In n set).
    (* extensionality *)
    intros. rewrite <- H in H1. eauto.
    (* base case *)
    intros. rewrite PTree.gempty in H. congruence.
    (* inductive case *)
    intros. rewrite PTree.gsspec in H2. rewrite add_spec.
    destruct (peq n k). auto. eauto.
  Qed.
End NodeSetForward.

Module NodeSetBackward <: NODE_SET.
  Definition t := PositiveSet.t.
  Definition add (n: positive) (s: t) : t := PositiveSet.add n s.
  Definition pick (s: t) :=
    match PositiveSet.min_elt s with
    | Some n => Some(n, PositiveSet.remove n s)
    | None => None
    end.
  Definition initial (successors: PTree.t (list positive)) :=
    PTree.fold (fun s pc scs => PositiveSet.add pc s) successors PositiveSet.empty.
  Definition In := PositiveSet.In.

  Lemma add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Proof NodeSetForward.add_spec.
    
  Lemma pick_none:
    forall s n, pick s = None -> ~In n s.
  Proof.
    intros until n; unfold pick. caseEq (PositiveSet.min_elt s); intros.
    congruence.
    apply PositiveSet.min_elt_3. auto.
  Qed.

  Lemma pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Proof.
    intros until s'; unfold pick. caseEq (PositiveSet.min_elt s); intros.
    inversion H0; clear H0; subst. 
    split; intros. 
    destruct (peq n n'). auto. right. apply PositiveSet.remove_2; assumption.
    elim H0; intro. subst n'. apply PositiveSet.min_elt_1. auto. 
    apply PositiveSet.remove_3 with n; assumption.
    congruence.
  Qed.

  Lemma initial_spec:
    forall successors n s, 
    successors!n = Some s -> In n (initial successors).
  Proof NodeSetForward.initial_spec.
End NodeSetBackward.


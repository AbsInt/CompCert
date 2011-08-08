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

(** Translation of parallel moves into sequences of individual moves.

  In this file, we adapt the generic "parallel move" algorithm
  (developed and proved correct in module [Parmov]) to the idiosyncraties
  of the [LTLin] and [Linear] intermediate languages.  While the generic
  algorithm assumes that registers never overlap, the locations
  used in [LTLin] and [Linear] can overlap, and assigning one location
  can set the values of other, overlapping locations to [Vundef].
  We address this issue in the remainder of this file.
*)

Require Import Coqlib.
Require Parmov.
Require Import Values.
Require Import Events.
Require Import AST.
Require Import Locations.
Require Import Conventions.

(** * Instantiating the generic parallel move algorithm *)

(** The temporary location to use for a move is determined
  by the type of the data being moved: register [IT2] for an
  integer datum, and register [FT2] for a floating-point datum. *)

Definition temp_for (l: loc) : loc :=
  match Loc.type l with Tint => R IT2 | Tfloat => R FT2 end.

Definition parmove (srcs dsts: list loc) :=
  Parmov.parmove2 loc Loc.eq temp_for srcs dsts.

Definition moves := (list (loc * loc))%type.

(** [exec_seq m] gives semantics to a sequence of elementary moves.
  This semantics ignores the possibility of overlap: only the
  target locations are updated, but the locations they
  overlap with are not set to [Vundef].  See [effect_seqmove] below
  for a semantics that accounts for overlaps. *)

Definition exec_seq (m: moves) (e: Locmap.t) : Locmap.t :=
  Parmov.exec_seq loc Loc.eq val m e.
  
Lemma temp_for_charact:
  forall l, temp_for l = R IT2 \/ temp_for l = R FT2.
Proof.
  intro; unfold temp_for. destruct (Loc.type l); tauto.
Qed.

Lemma is_not_temp_charact:
  forall l,
  Parmov.is_not_temp loc temp_for l <-> l <> R IT2 /\ l <> R FT2.
Proof.
  intros. unfold Parmov.is_not_temp. 
  destruct (Loc.eq l (R IT2)). 
  subst l. intuition. apply (H (R IT2)). reflexivity. discriminate.
  destruct (Loc.eq l (R FT2)).
  subst l. intuition. apply (H (R FT2)). reflexivity. 
  assert (forall d, l <> temp_for d). 
    intro. elim (temp_for_charact d); congruence.
  intuition. 
Qed.

Lemma disjoint_temp_not_temp:
  forall l, Loc.notin l temporaries -> Parmov.is_not_temp loc temp_for l.
Proof.
  intros. rewrite is_not_temp_charact. 
  unfold temporaries in H; simpl in H. 
  split; apply Loc.diff_not_eq; tauto.
Qed.

Lemma loc_norepet_norepet:
  forall l, Loc.norepet l -> list_norepet l.
Proof.
  induction 1; constructor. 
  apply Loc.notin_not_in; auto. auto.
Qed.

(** Instantiating the theorems proved in [Parmov], we obtain
  the following properties of semantic correctness and well-typedness
  of the generated sequence of moves.  Note that the semantic
  correctness result is stated in terms of the [exec_seq] semantics,
  and therefore does not account for overlap between locations. *)

Lemma parmove_prop_1:
  forall srcs dsts,
  List.length srcs = List.length dsts ->
  Loc.norepet dsts ->
  Loc.disjoint srcs temporaries ->
  Loc.disjoint dsts temporaries ->
  forall e,
  let e' := exec_seq (parmove srcs dsts) e in
  List.map e' dsts = List.map e srcs /\
  forall l, ~In l dsts -> l <> R IT2 -> l <> R FT2 -> e' l = e l.
Proof.
  intros. 
  assert (NR: list_norepet dsts) by (apply loc_norepet_norepet; auto).
  assert (NTS: forall r, In r srcs -> Parmov.is_not_temp loc temp_for r).
    intros. apply disjoint_temp_not_temp. apply Loc.disjoint_notin with srcs; auto.
  assert (NTD: forall r, In r dsts -> Parmov.is_not_temp loc temp_for r).
    intros. apply disjoint_temp_not_temp. apply Loc.disjoint_notin with dsts; auto.
  generalize (Parmov.parmove2_correctness loc Loc.eq temp_for val srcs dsts H NR NTS NTD e).
  change (Parmov.exec_seq loc Loc.eq val (Parmov.parmove2 loc Loc.eq temp_for srcs dsts) e) with e'.
  intros [A B].
  split. auto. intros. apply B. auto. rewrite is_not_temp_charact; auto.
Qed.

Lemma parmove_prop_2:
  forall srcs dsts s d,
  In (s, d) (parmove srcs dsts) ->
     (In s srcs \/ s = R IT2 \/ s = R FT2)
  /\ (In d dsts \/ d = R IT2 \/ d = R FT2).
Proof.
  intros srcs dsts.
  set (mu := List.combine srcs dsts).
  assert (forall s d, Parmov.wf_move loc temp_for mu s d ->
            (In s srcs \/ s = R IT2 \/ s = R FT2)
         /\ (In d dsts \/ d = R IT2 \/ d = R FT2)).
  unfold mu; induction 1. 
  split. 
    left. eapply List.in_combine_l; eauto.
    left. eapply List.in_combine_r; eauto.
  split. 
    right. apply temp_for_charact. 
    tauto.
  split.
    tauto.
    right. apply temp_for_charact.
  intros. apply H. 
  apply (Parmov.parmove2_wf_moves loc Loc.eq temp_for srcs dsts s d H0). 
Qed.

Lemma loc_type_temp_for:
  forall l, Loc.type (temp_for l) = Loc.type l.
Proof.
  intros; unfold temp_for. destruct (Loc.type l); reflexivity. 
Qed.

Lemma loc_type_combine:
  forall srcs dsts,
  List.map Loc.type srcs = List.map Loc.type dsts ->
  forall s d,
  In (s, d) (List.combine srcs dsts) ->
  Loc.type s = Loc.type d.
Proof.
  induction srcs; destruct dsts; simpl; intros; try discriminate.
  elim H0.
  elim H0; intros. inversion H1; subst. congruence.
  apply IHsrcs with dsts. congruence. auto.
Qed.

Lemma parmove_prop_3:
  forall srcs dsts,
  List.map Loc.type srcs = List.map Loc.type dsts ->
  forall s d,
  In (s, d) (parmove srcs dsts) -> Loc.type s = Loc.type d.
Proof.
  intros srcs dsts TYP.
  set (mu := List.combine srcs dsts).
  assert (forall s d, Parmov.wf_move loc temp_for mu s d ->
            Loc.type s = Loc.type d).
  unfold mu; induction 1. 
  eapply loc_type_combine; eauto.
  rewrite loc_type_temp_for; auto.
  rewrite loc_type_temp_for; auto.
  intros. apply H. 
  apply (Parmov.parmove2_wf_moves loc Loc.eq temp_for srcs dsts s d H0). 
Qed.

(** * Accounting for overlap between locations *)

Section EQUIVALENCE.

(** We now prove the correctness of the generated sequence of elementary
  moves, accounting for possible overlap between locations.
  The proof is conducted under the following hypotheses: there must
  be no partial overlap between
- two distinct destinations (hypothesis [NOREPET]);
- a source location and a destination location (hypothesis [NO_OVERLAP]).
*)

Variables srcs dsts: list loc.
Hypothesis LENGTH: List.length srcs = List.length dsts.
Hypothesis NOREPET: Loc.norepet dsts.
Hypothesis NO_OVERLAP: Loc.no_overlap srcs dsts.
Hypothesis NO_SRCS_TEMP: Loc.disjoint srcs temporaries.
Hypothesis NO_DSTS_TEMP: Loc.disjoint dsts temporaries.

(** [no_overlap_dests l] holds if location [l] does not partially overlap
  a destination location: either it is identical to one of the
  destinations, or it is disjoint from all destinations. *)

Definition no_overlap_dests (l: loc) : Prop :=
  forall d, In d dsts -> l = d \/ Loc.diff l d.

(** We show that [no_overlap_dests] holds for any destination location
  and for any source location. *)

Lemma dests_no_overlap_dests:
  forall l, In l dsts -> no_overlap_dests l.
Proof.
  assert (forall d, Loc.norepet d ->
          forall l1 l2, In l1 d -> In l2 d -> l1 = l2 \/ Loc.diff l1 l2).
  induction 1; simpl; intros.
  contradiction.
  elim H1; intro; elim H2; intro.
  left; congruence.
  right. subst l1. eapply Loc.in_notin_diff; eauto.
  right. subst l2. apply Loc.diff_sym. eapply Loc.in_notin_diff; eauto.
  eauto.
  intros; red; intros. eauto. 
Qed.

Lemma notin_dests_no_overlap_dests:
  forall l, Loc.notin l dsts -> no_overlap_dests l.
Proof.
  intros; red; intros.
  right. eapply Loc.in_notin_diff; eauto.
Qed.

Lemma source_no_overlap_dests:
  forall s, In s srcs \/ s = R IT2 \/ s = R FT2 -> no_overlap_dests s.
Proof.
  intros. elim H; intro. exact (NO_OVERLAP s H0). 
  elim H0; intro; subst s; red; intros;
  right; apply Loc.diff_sym; apply NO_DSTS_TEMP; auto; simpl; tauto.
Qed.

Lemma source_not_temp1:
  forall s, In s srcs \/ s = R IT2 \/ s = R FT2 -> 
  Loc.diff s (R IT1) /\ Loc.diff s (R FT1) /\ Loc.notin s destroyed_at_move.
Proof.
  intros. destruct H.
  exploit Loc.disjoint_notin. eexact NO_SRCS_TEMP. eauto. 
  simpl; tauto.
  destruct H; subst s; simpl; intuition congruence.
Qed.

Lemma dest_noteq_diff:
  forall d l, 
  In d dsts \/ d = R IT2 \/ d = R FT2 ->
  l <> d ->
  no_overlap_dests l ->
  Loc.diff l d.
Proof.
  intros. elim H; intro.
  elim (H1 d H2); intro. congruence. auto.
  assert (forall r, l <> R r -> Loc.diff l (R r)).
    intros. destruct l; simpl. congruence. destruct s; auto.
  elim H2; intro; subst d; auto.
Qed.

(** [locmap_equiv e1 e2] holds if the location maps [e1] and [e2]
  assign the same values to all locations except temporaries [IT1], [FT1]
  and except locations that partially overlap a destination. *)

Definition locmap_equiv (e1 e2: Locmap.t): Prop :=
  forall l,
  no_overlap_dests l -> Loc.diff l (R IT1) -> Loc.diff l (R FT1) -> Loc.notin l destroyed_at_move -> e2 l = e1 l.

(** The following predicates characterize the effect of one move
  move ([effect_move]) and of a sequence of elementary moves
  ([effect_seqmove]).  We allow the code generated for one move
  to use the temporaries [IT1] and [FT1] and [destroyed_at_move] in any way it needs. *)

Definition effect_move (src dst: loc) (e e': Locmap.t): Prop :=
  e' dst = e src /\
  forall l, Loc.diff l dst -> Loc.diff l (R IT1) -> Loc.diff l (R FT1) -> Loc.notin l destroyed_at_move -> e' l = e l.

Inductive effect_seqmove: list (loc * loc) -> Locmap.t -> Locmap.t -> Prop :=
  | effect_seqmove_nil: forall e,
      effect_seqmove nil e e
  | effect_seqmove_cons: forall s d m e1 e2 e3,
      effect_move s d e1 e2 ->
      effect_seqmove m e2 e3 ->
      effect_seqmove ((s, d) :: m) e1 e3.

(** The following crucial lemma shows that [locmap_equiv] is preserved
  by executing one move [d <- s], once using the [effect_move]
  predicate that accounts for partial overlap and the use of
  temporaries [IT1], [FT1], or via the [Parmov.update] function that
  does not account for any of these. *)

Lemma effect_move_equiv:
  forall s d e1 e2 e1',
  (In s srcs \/ s = R IT2 \/ s = R FT2) ->
  (In d dsts \/ d = R IT2 \/ d = R FT2) ->
  locmap_equiv e1 e2 -> effect_move s d e1 e1' ->
  locmap_equiv e1' (Parmov.update loc Loc.eq val d (e2 s) e2).
Proof.
  intros. destruct H2. red; intros. 
  unfold Parmov.update. destruct (Loc.eq l d). 
  subst l. destruct (source_not_temp1 _ H) as [A [B C]]. 
  rewrite H2. apply H1; auto. apply source_no_overlap_dests; auto.
  rewrite H3; auto. apply dest_noteq_diff; auto. 
Qed.

(** We then extend the previous lemma to a sequence [mu] of elementary moves.
*)

Lemma effect_seqmove_equiv:
  forall mu e1 e1',
  effect_seqmove mu e1 e1' ->
  forall e2,
  (forall s d, In (s, d) mu ->
     (In s srcs \/ s = R IT2 \/ s = R FT2) /\
     (In d dsts \/ d = R IT2 \/ d = R FT2)) ->
  locmap_equiv e1 e2 ->
  locmap_equiv e1' (exec_seq mu e2).
Proof.
  induction 1; intros.
  simpl. auto.
  simpl. apply IHeffect_seqmove. 
  intros. apply H1. apply in_cons; auto. 
  destruct (H1 s d (in_eq _ _)).
  eapply effect_move_equiv; eauto. 
Qed.

(** Here is the main result in this file: executing the sequence
  of moves returned by the [parmove] function results in the
  desired state for locations: the final values of destination locations
  are the initial values of source locations, and all locations
  that are disjoint from the temporaries and the destinations
  keep their initial values. *)

Lemma effect_parmove:
  forall e e',
  effect_seqmove (parmove srcs dsts) e e' ->
  List.map e' dsts = List.map e srcs /\
  forall l, Loc.notin l dsts -> Loc.notin l temporaries -> e' l = e l.
Proof.
  set (mu := parmove srcs dsts). intros.
  assert (locmap_equiv e e) by (red; auto).
  generalize (effect_seqmove_equiv mu e e' H e (parmove_prop_2 srcs dsts) H0).
  intro. 
  generalize (parmove_prop_1 srcs dsts LENGTH NOREPET NO_SRCS_TEMP NO_DSTS_TEMP e).
  fold mu. intros [A B]. 
  (* e' dsts = e srcs *)
  split. rewrite <- A. apply list_map_exten; intros.
  exploit Loc.disjoint_notin. eexact NO_DSTS_TEMP. eauto. simpl; intros.
  apply H1. apply dests_no_overlap_dests; auto.
  tauto. tauto. simpl; tauto. 
  (* other locations *)
  intros. transitivity (exec_seq mu e l). 
  symmetry. apply H1. apply notin_dests_no_overlap_dests; auto.
  eapply Loc.in_notin_diff; eauto. simpl; tauto.
  eapply Loc.in_notin_diff; eauto. simpl; tauto.
  simpl in H3; simpl; tauto.
  apply B. apply Loc.notin_not_in; auto.
  apply Loc.diff_not_eq. eapply Loc.in_notin_diff; eauto. simpl; tauto.
  apply Loc.diff_not_eq. eapply Loc.in_notin_diff; eauto. simpl; tauto.
Qed.

End EQUIVALENCE.


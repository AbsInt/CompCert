Require Import Coqlib.
Require Parmov.
Require Import Values.
Require Import Events.
Require Import AST.
Require Import Locations.
Require Import Conventions.

Definition temp_for (l: loc) : loc :=
  match Loc.type l with Tint => R IT2 | Tfloat => R FT2 end.

Definition parmove (srcs dsts: list loc) :=
  Parmov.parmove2 loc temp_for Loc.eq srcs dsts.

Definition moves := (list (loc * loc))%type.

Definition exec_seq (m: moves) (e: Locmap.t) : Locmap.t :=
  Parmov.exec_seq loc val Loc.eq m e.
  
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
  generalize (Parmov.parmove2_correctness loc temp_for val Loc.eq srcs dsts H NR NTS NTD e).
  change (Parmov.exec_seq loc val Loc.eq (Parmov.parmove2 loc temp_for Loc.eq srcs dsts) e) with e'.
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
  apply (Parmov.parmove2_wf_moves loc temp_for Loc.eq srcs dsts s d H0). 
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
  apply (Parmov.parmove2_wf_moves loc temp_for Loc.eq srcs dsts s d H0). 
Qed.

Section EQUIVALENCE.

Variables srcs dsts: list loc.
Hypothesis LENGTH: List.length srcs = List.length dsts.
Hypothesis NOREPET: Loc.norepet dsts.
Hypothesis NO_OVERLAP: Loc.no_overlap srcs dsts.
Hypothesis NO_SRCS_TEMP: Loc.disjoint srcs temporaries.
Hypothesis NO_DSTS_TEMP: Loc.disjoint dsts temporaries.

Definition no_overlap_dests (l: loc) : Prop :=
  forall d, In d dsts -> l = d \/ Loc.diff l d.

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
  forall s, In s srcs \/ s = R IT2 \/ s = R FT2 -> Loc.diff s (R IT1) /\ Loc.diff s (R FT1).
Proof.
  intros. elim H; intro. 
  split; apply NO_SRCS_TEMP; auto; simpl; tauto.
  elim H0; intro; subst s; simpl; split; congruence.
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

Definition locmap_equiv (e1 e2: Locmap.t): Prop :=
  forall l,
  no_overlap_dests l -> Loc.diff l (R IT1) -> Loc.diff l (R FT1) -> e2 l = e1 l.

Definition effect_move (src dst: loc) (e e': Locmap.t): Prop :=
  e' dst = e src /\
  forall l, Loc.diff l dst -> Loc.diff l (R IT1) -> Loc.diff l (R FT1) -> e' l = e l.

Inductive effect_seqmove: list (loc * loc) -> Locmap.t -> Locmap.t -> Prop :=
  | effect_seqmove_nil: forall e,
      effect_seqmove nil e e
  | effect_seqmove_cons: forall s d m e1 e2 e3,
      effect_move s d e1 e2 ->
      effect_seqmove m e2 e3 ->
      effect_seqmove ((s, d) :: m) e1 e3.

Lemma effect_move_equiv:
  forall s d e1 e2 e1',
  (In s srcs \/ s = R IT2 \/ s = R FT2) ->
  (In d dsts \/ d = R IT2 \/ d = R FT2) ->
  locmap_equiv e1 e2 -> effect_move s d e1 e1' ->
  locmap_equiv e1' (Parmov.update loc val Loc.eq d (e2 s) e2).
Proof.
  intros. destruct H2. red; intros. 
  unfold Parmov.update. destruct (Loc.eq l d). 
  subst l. elim (source_not_temp1 _ H); intros.
  rewrite H2. apply H1; auto. apply source_no_overlap_dests; auto.
  rewrite H3; auto. apply dest_noteq_diff; auto. 
Qed.

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

Lemma effect_parmove:
  forall e e',
  effect_seqmove (parmove srcs dsts) e e' ->
  List.map e' dsts = List.map e srcs /\
  e' (R IT3) = e (R IT3) /\
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
  apply H1. apply dests_no_overlap_dests; auto.
  apply NO_DSTS_TEMP; auto; simpl; tauto.
  apply NO_DSTS_TEMP; auto; simpl; tauto.
  (* e' IT3 = e IT3 *)
  split. 
  assert (Loc.notin (R IT3) dsts).
  apply Loc.disjoint_notin with temporaries. 
  apply Loc.disjoint_sym; auto. simpl; tauto. 
  transitivity (exec_seq mu e (R IT3)). 
  symmetry. apply H1. apply notin_dests_no_overlap_dests. auto.
  simpl; congruence. simpl; congruence.
  apply B. apply Loc.notin_not_in; auto. congruence. congruence.
  (* other locations *)
  intros. transitivity (exec_seq mu e l). 
  symmetry. apply H1. apply notin_dests_no_overlap_dests; auto.
  eapply Loc.in_notin_diff; eauto. simpl; tauto.
  eapply Loc.in_notin_diff; eauto. simpl; tauto.
  apply B. apply Loc.notin_not_in; auto.
  apply Loc.diff_not_eq. eapply Loc.in_notin_diff; eauto. simpl; tauto.
  apply Loc.diff_not_eq. eapply Loc.in_notin_diff; eauto. simpl; tauto.
Qed.

End EQUIVALENCE.


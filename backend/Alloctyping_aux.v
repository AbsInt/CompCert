(** Type preservation for parallel move compilation. *)

(** This file, contributed by Laurence Rideau, shows that the parallel
  move compilation algorithm (file [Parallelmove]) generates a well-typed
  sequence of LTL instructions, provided the original problem is well-typed:
  the types of source and destination locations match pairwise. *)

Require Import Coqlib.
Require Import Locations.
Require Import LTL.
Require Import Allocation.
Require Import LTLtyping.
Require Import Allocproof_aux.
Require Import Parallelmove.
Require Import Inclusion.

Section wt_move_correction.
Variable tf : LTL.function.
Variable loc_read_ok : loc ->  Prop.
Hypothesis loc_read_ok_R : forall r,  loc_read_ok (R r).
Variable loc_write_ok : loc ->  Prop.
Hypothesis loc_write_ok_R : forall r,  loc_write_ok (R r).
 
Let locs_read_ok (ll : list loc) : Prop :=
   forall l, In l ll ->  loc_read_ok l.
 
Let locs_write_ok (ll : list loc) : Prop :=
   forall l, In l ll ->  loc_write_ok l.

Hypothesis
   wt_add_move :
   forall (src dst : loc) (b : LTL.block),
   loc_read_ok src ->
   loc_write_ok dst ->
   Loc.type src = Loc.type dst ->
   wt_block tf b ->  wt_block tf (add_move src dst b).
 
Lemma in_move__in_srcdst:
 forall m p, In m p ->  In (fst m) (getsrc p) /\ In (snd m) (getdst p).
Proof.
intros; induction p.
inversion H.
destruct a as [a1 a2]; destruct m as [m1 m2]; simpl.
elim H; intro.
inversion H0.
subst a2; subst a1.
split; [left; trivial | left; trivial].
split; right; (elim IHp; simpl; intros; auto).
Qed.
 
Lemma T_type: forall r,  Loc.type r = Loc.type (T r).
Proof.
intro; unfold T.
case (Loc.type r); auto.
Qed.
 
Theorem incl_nil: forall A (l : list A),  incl nil l.
Proof.
intros A l a; simpl; intros H; case H.
Qed.
Hint Resolve incl_nil :datatypes.
 
Lemma split_move_incl:
 forall (l t1 t2 : Moves) (s d : Reg),
 split_move l s = Some (t1, d, t2) ->  incl t1 l /\ incl t2 l.
Proof.
induction l.
simpl; (intros; discriminate).
intros t1 t2 s d; destruct a as [a1 a2]; simpl.
case (Loc.eq a1 s); intro.
intros.
inversion H.
split; auto.
apply incl_nil.
apply incl_tl; apply incl_refl; auto.
caseEq (split_move l s); intro; (try (intros; discriminate)).
destruct p as [[p1 p2] p3].
intros.
inversion H0.
elim (IHl p1 p3 s p2); intros; auto.
subst p3.
split; auto.
generalize H1; unfold incl; simpl.
intros H4 a [H7|H6]; [try exact H7 | idtac].
left; (try assumption).
right; apply H4; auto.
apply incl_tl; auto.
Qed.
 
Lemma in_split_move:
 forall (l t1 t2 : Moves) (s d : Reg),
 split_move l s = Some (t1, d, t2) ->  In (s, d) l.
Proof.
induction l.
simpl; intros; discriminate.
intros t1 t2 s d; simpl.
destruct a as [a1 a2].
case (Loc.eq a1 s).
intros.
inversion H.
subst a1; left; auto.
intro; caseEq (split_move l s); (intros; (try discriminate)).
destruct p as [[p1 p2] p3].
right; inversion H0.
subst p2.
apply (IHl p1 p3); auto.
Qed.
 
Lemma move_types_stepf:
 forall S1,
 (forall x1 x2,
  In (x1, x2) (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1)) ->
   Loc.type x1 = Loc.type x2) ->
 forall x1 x2,
 In
  (x1, x2)
  (StateToMove (stepf S1) ++ (StateBeing (stepf S1) ++ StateDone (stepf S1))) ->
  Loc.type x1 = Loc.type x2.
Proof.
intros S1 H x1 x2.
destruct S1 as [[t1 b1] d1]; set (S1:=(t1, b1, d1)); destruct t1; destruct b1;
 auto; simpl StateToMove in H |-; simpl StateBeing in H |-;
 simpl StateDone in H |-; simpl app in H |-.
intro;
 elim
  (in_app_or
    (StateToMove (stepf S1)) (StateBeing (stepf S1) ++ StateDone (stepf S1))
    (x1, x2)); auto.
assert (StateToMove (stepf S1) = nil).
simpl stepf.
destruct m as [s d].
case (Loc.eq d (fst (last b1))); case b1; simpl; auto.
rewrite H1; intros H2; inversion H2.
intro; elim (in_app_or (StateBeing (stepf S1)) (StateDone (stepf S1)) (x1, x2));
 auto.
assert
 (StateBeing (stepf S1) = nil \/
  (StateBeing (stepf S1) = b1 \/ StateBeing (stepf S1) = replace_last_s b1)).
simpl stepf.
destruct m as [s d].
case (Loc.eq d (fst (last b1))); case b1; simpl; auto.
elim H2; [intros H3; (try clear H2); (try exact H3) | intros H3; (try clear H2)].
rewrite H3; intros H4; inversion H4.
elim H3; [intros H2; (try clear H3); (try exact H2) | intros H2; (try clear H3)].
rewrite H2; intros H4.
apply H; (try in_tac).
rewrite H2; intros H4.
caseEq b1; intro; simpl; auto.
rewrite H3 in H4; simpl in H4 |-; inversion H4.
intros l H5; rewrite H5 in H4.
generalize (app_rewriter _ l m0).
intros [y [r H3]]; (try exact H3).
rewrite H3 in H4.
destruct y.
rewrite last_replace in H4.
elim (in_app_or r ((T r0, r1) :: nil) (x1, x2)); auto.
intro; apply H.
rewrite H5.
rewrite H3; in_tac.
intros H6; inversion H6.
inversion H7.
rewrite <- T_type.
rewrite <- H10; apply H.
rewrite H5; rewrite H3; (try in_tac).
assert (In (r0, r1) ((r0, r1) :: nil)); [simpl; auto | in_tac].
inversion H7.
intro.
destruct m as [s d].
assert
 (StateDone (stepf S1) = (s, d) :: d1 \/
  StateDone (stepf S1) = (s, d) :: ((d, T d) :: d1)).
simpl.
case (Loc.eq d (fst (last b1))); case b1; simpl; auto.
elim H3; [intros H4; (try clear H3); (try exact H4) | intros H4; (try clear H3)].
apply H; (try in_tac).
rewrite H4 in H2; in_tac.
rewrite H4 in H2.
simpl in H2 |-.
elim H2; [intros H3; apply H | intros H3; elim H3; intros; [idtac | apply H]];
 (try in_tac).
simpl; left; auto.
inversion H5; apply T_type.
intro;
 elim
  (in_app_or
    (StateToMove (stepf S1)) (StateBeing (stepf S1) ++ StateDone (stepf S1))
    (x1, x2)); auto.
simpl stepf.
destruct m as [s d].
case (Loc.eq s d); simpl; intros; apply H; in_tac.
intro; elim (in_app_or (StateBeing (stepf S1)) (StateDone (stepf S1)) (x1, x2));
 auto.
simpl stepf.
destruct m as [s d].
case (Loc.eq s d); intros; apply H; (try in_tac).
inversion H2.
simpl stepf.
destruct m as [s d].
case (Loc.eq s d); intros; apply H; (try in_tac).
simpl in H2 |-; in_tac.
simpl in H2 |-; in_tac.
intro;
 elim
  (in_app_or
    (StateToMove (stepf S1)) (StateBeing (stepf S1) ++ StateDone (stepf S1))
    (x1, x2)); auto.
simpl stepf.
destruct m as [s d].
destruct m0 as [s0 d0].
case (Loc.eq s d0); [simpl; intros; apply H; in_tac | idtac].
caseEq (split_move t1 d0); intro.
destruct p as [[t2 b2] d2].
intros Hsplit Hd; simpl StateToMove; intro.
elim (split_move_incl t1 t2 d2 d0 b2 Hsplit); auto.
intros; apply H.
assert (In (x1, x2) ((s, d) :: (t1 ++ t1))).
generalize H1; simpl; intros.
elim H4; [intros H5; left; (try exact H5) | intros H5; right].
elim (in_app_or t2 d2 (x1, x2)); auto; intro; apply in_or_app; left.
unfold incl in H2 |-.
apply H2; auto.
unfold incl in H3 |-; apply H3; auto.
in_tac.
intro; case (Loc.eq d0 (fst (last b1))); case b1; auto; simpl StateToMove;
 intros; apply H; in_tac.
intro; elim (in_app_or (StateBeing (stepf S1)) (StateDone (stepf S1)) (x1, x2));
 auto.
simpl stepf.
destruct m as [s d].
destruct m0 as [s0 d0].
case (Loc.eq s d0).
intros e; rewrite <- e; simpl StateBeing.
rewrite <- e in H.
intro; apply H; in_tac.
caseEq (split_move t1 d0); intro.
destruct p as [[t2 b2] d2].
simpl StateBeing.
intros.
apply H.
generalize (in_split_move t1 t2 d2 d0 b2 H2).
intros.
elim H3; intros.
rewrite <- H5.
in_tac.
in_tac.
caseEq b1.
simpl; intros e n F; elim F.
intros m l H3 H4.
case (Loc.eq d0 (fst (last (m :: l)))).
generalize (app_rewriter Move l m).
intros [y [r H5]]; rewrite H5.
simpl StateBeing.
destruct y as [y1 y2]; generalize (last_replace r y1 y2).
simpl; intros heq H6.
unfold Move in heq |-; unfold Move.
rewrite heq.
intro.
elim (in_app_or r ((T y1, y2) :: nil) (x1, x2)); auto.
intro; apply H.
rewrite H3; rewrite H5; in_tac.
simpl; intros [H8|H8]; inversion H8.
rewrite <- T_type.
apply H.
rewrite H3; rewrite H5.
rewrite <- H11; assert (In (y1, y2) ((y1, y2) :: nil)); auto.
simpl; auto.
in_tac.
simpl StateBeing; intros.
apply H; rewrite H3; (try in_tac).
simpl stepf.
destruct m as [s d].
destruct m0 as [s0 d0].
case (Loc.eq s d0); [simpl; intros; apply H; in_tac | idtac].
caseEq (split_move t1 d0); intro.
destruct p as [[t2 b2] d2].
intros Hsplit Hd; simpl StateDone; intro.
apply H; (try in_tac).
case (Loc.eq d0 (fst (last b1))); case b1; simpl StateDone; intros;
 (try (apply H; in_tac)).
elim H3; intros.
apply H.
assert (In (x1, x2) ((s0, d0) :: nil)); auto.
rewrite H4; auto.
simpl; left; auto.
in_tac.
elim H4; intros.
inversion H5; apply T_type.
apply H; in_tac.
Qed.
 
Lemma move_types_res:
 forall S1,
 (forall x1 x2,
  In (x1, x2) (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1)) ->
   Loc.type x1 = Loc.type x2) ->
 forall x1 x2,
 In
  (x1, x2)
  (StateToMove (Pmov S1) ++ (StateBeing (Pmov S1) ++ StateDone (Pmov S1))) ->
  Loc.type x1 = Loc.type x2.
Proof.
intros S1; elim S1  using (well_founded_ind (Wf_nat.well_founded_ltof _ mesure)).
clear S1; intros S1 Hrec.
destruct S1 as [[t b] d]; set (S1:=(t, b, d)).
unfold S1; rewrite Pmov_equation; intros.
destruct t; auto.
destruct b; auto.
apply (Hrec (stepf S1)).
apply stepf1_dec; auto.
apply move_types_stepf; auto.
unfold S1; auto.
apply (Hrec (stepf S1)).
apply stepf1_dec; auto.
apply move_types_stepf; auto.
unfold S1; auto.
Qed.
 
Lemma srcdst_tmp2_stepf:
 forall S1 x1 x2,
 In
  (x1, x2)
  (StateToMove (stepf S1) ++ (StateBeing (stepf S1) ++ StateDone (stepf S1))) ->
  (In x1 temporaries2 \/
   In x1 (getsrc (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1)))) /\
  (In x2 temporaries2 \/
   In x2 (getdst (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1)))).
Proof.
intros S1 x1 x2 H.
(repeat rewrite getsrc_app); (repeat rewrite getdst_app).
destruct S1 as [[t1 b1] d1]; set (S1:=(t1, b1, d1)); destruct t1; destruct b1;
 auto.
simpl in H |-.
elim (in_move__in_srcdst (x1, x2) d1); intros; auto.
elim
 (in_app_or
   (StateToMove (stepf S1)) (StateBeing (stepf S1) ++ StateDone (stepf S1))
   (x1, x2)); auto.
assert (StateToMove (stepf S1) = nil).
simpl stepf.
destruct m as [s d].
case (Loc.eq d (fst (last b1))); case b1; simpl; auto.
rewrite H0; intros H2; inversion H2.
intro; elim (in_app_or (StateBeing (stepf S1)) (StateDone (stepf S1)) (x1, x2));
 auto.
simpl stepf.
destruct m as [s d].
caseEq b1.
simpl.
intros h1 h2; inversion h2.
intros m l heq; generalize (app_rewriter _ l m).
intros [y [r H3]]; (try exact H3).
rewrite H3.
destruct y.
rewrite last_app; simpl fst.
case (Loc.eq d r0).
intros heqd.
rewrite last_replace.
simpl.
intro; elim (in_app_or r ((T r0, r1) :: nil) (x1, x2)); auto.
rewrite heq; rewrite H3.
rewrite getsrc_app; simpl; rewrite getdst_app; simpl.
intro; elim (in_move__in_srcdst (x1, x2) r); auto; simpl; intros; split; right;
 right; in_tac.
intro.
inversion H2; inversion H4.
split.
unfold T; case (Loc.type r0); left; [left | right]; auto.
right; right; (try assumption).
rewrite heq; rewrite H3.
rewrite H7; simpl.
rewrite getdst_app; simpl.
assert (In x2 (x2 :: nil)); simpl; auto.
in_tac.
simpl StateBeing.
intros; elim (in_move__in_srcdst (x1, x2) (r ++ ((r0, r1) :: nil))); auto;
 intros; split; right; right.
unfold snd in H4 |-; unfold fst in H2 |-; rewrite heq; rewrite H3; (try in_tac).
unfold snd in H4 |-; unfold fst in H2 |-; rewrite heq; rewrite H3; (try in_tac).
simpl stepf.
destruct m as [s d].
caseEq b1; intro.
simpl StateDone; intro.
unfold S1, StateToMove, StateBeing.
simpl app.
elim (in_move__in_srcdst (x1, x2) ((s, d) :: d1)); auto; intros; split; right.
simpl snd in H4 |-; simpl fst in H3 |-; simpl getdst in H4 |-;
 simpl getsrc in H3 |-; (try in_tac).
simpl snd in H4 |-; simpl fst in H3 |-; simpl getdst in H4 |-;
 simpl getsrc in H3 |-; (try in_tac).
intros; generalize (app_rewriter _ l m).
intros [y [r H4]].
generalize H2; rewrite H4; rewrite last_app.
destruct y as [y1 y2].
simpl fst.
case (Loc.eq d y1).
simpl StateDone; intros.
elim H3; [intros H6; inversion H6; (try exact H6) | intros H6; (try clear H5)].
simpl; split; right; left; auto.
elim H6; [intros H5; inversion H5; (try exact H5) | intros H5; (try clear H6)].
split; [right; simpl; right | left].
rewrite H1; rewrite H4; rewrite getsrc_app; simpl getsrc.
rewrite <- e; rewrite H8; assert (In x1 (x1 :: nil)); simpl; auto; (try in_tac).
unfold T; case (Loc.type x1); simpl; auto.
elim (in_move__in_srcdst (x1, x2) d1); auto; intros; split; right; right;
 (try in_tac).
intro; simpl StateDone.
unfold S1, StateToMove, StateBeing, StateDone.
simpl getsrc; simpl app; (try in_tac).
intro; elim (in_move__in_srcdst (x1, x2) ((s, d) :: d1));
 (auto; (simpl fst; simpl snd; simpl getsrc; simpl getdst); intros);
 (split; right; (try in_tac)).
unfold S1, StateToMove, StateBeing, StateDone.
elim
 (in_app_or
   (StateToMove (stepf S1)) (StateBeing (stepf S1) ++ StateDone (stepf S1))
   (x1, x2)); auto.
simpl stepf.
destruct m as [s d].
case (Loc.eq s d).
simpl StateToMove.
intros; elim (in_move__in_srcdst (x1, x2) t1); auto;
 (repeat (rewrite getsrc_app; simpl getsrc));
 (repeat (rewrite getdst_app; simpl getdst)); simpl fst; simpl snd; intros;
 split; right; simpl; right; (try in_tac).
simpl StateToMove.
intros; elim (in_move__in_srcdst (x1, x2) t1); auto;
 (repeat (rewrite getsrc_app; simpl getsrc));
 (repeat (rewrite getdst_app; simpl getdst)); simpl fst; simpl snd; intros;
 split; right; simpl; right; (try in_tac).
intro; elim (in_app_or (StateBeing (stepf S1)) (StateDone (stepf S1)) (x1, x2));
 auto.
simpl stepf.
destruct m as [s d].
case (Loc.eq s d).
simpl StateBeing; intros h1 h2; inversion h2.
simpl StateBeing; intros h1 h2.
elim (in_move__in_srcdst (x1, x2) ((s, d) :: nil)); auto; simpl fst; simpl snd;
 simpl; intros; split; right; (try in_tac).
elim H1; [intros H3; left; (try exact H3) | intros H3; inversion H3].
elim H2; [intros H3; left; (try exact H3) | intros H3; inversion H3].
simpl stepf.
destruct m as [s d].
case (Loc.eq s d).
simpl StateDone; intros h1 h2.
elim (in_move__in_srcdst (x1, x2) d1); auto; simpl fst; simpl snd; simpl;
 intros; split; right; right; (try in_tac).
simpl StateDone; intros h1 h2.
elim (in_move__in_srcdst (x1, x2) d1); auto; simpl fst; simpl snd; simpl;
 intros; split; right; right; (try in_tac).
elim
 (in_app_or
   (StateToMove (stepf S1)) (StateBeing (stepf S1) ++ StateDone (stepf S1))
   (x1, x2)); auto.
simpl stepf.
destruct m as [s d].
destruct m0 as [s0 d0].
case (Loc.eq s d0).
unfold S1, StateToMove, StateBeing, StateDone.
simpl app at 1.
intros; elim (in_move__in_srcdst (x1, x2) t1);
 (auto; simpl; intros; (split; right; right; (try in_tac))).
intro; caseEq (split_move t1 d0); intro.
destruct p as [[t2 b2] d2].
intros Hsplit; unfold S1, StateToMove, StateBeing, StateDone; intro.
elim (split_move_incl t1 t2 d2 d0 b2 Hsplit); auto.
intros.
assert (In (x1, x2) ((s, d) :: (t1 ++ t1))).
generalize H0; simpl; intros.
elim H3; [intros H5; left; (try exact H5) | intros H5; right].
elim (in_app_or t2 d2 (x1, x2)); auto; intro; apply in_or_app; left.
unfold incl in H1 |-.
apply H1; auto.
unfold incl in H2 |-; apply H2; auto.
split; right.
elim (in_move__in_srcdst (x1, x2) ((s, d) :: (t1 ++ t1)));
 (auto; simpl; intros; (try in_tac)).
elim H4; [intros H6; (try clear H4); (try exact H6) | intros H6; (try clear H4)].
left; (try assumption).
right; (try in_tac).
rewrite getsrc_app in H6; (try in_tac).
elim (in_move__in_srcdst (x1, x2) ((s, d) :: (t1 ++ t1)));
 (auto; simpl; intros; (try in_tac)).
elim H5; [intros H6; (try clear H5); (try exact H6) | intros H6; (try clear H5)].
left; (try assumption).
right; rewrite getdst_app in H6; (try in_tac).
caseEq b1; intro.
unfold S1, StateToMove, StateBeing, StateDone.
intro; elim (in_move__in_srcdst (x1, x2) ((s, d) :: t1)); (auto; intros).
simpl snd in H4 |-; simpl fst in H3 |-; split; right; (try in_tac).
intros l heq; generalize (app_rewriter _ l m).
intros [y [r H1]]; rewrite H1.
destruct y as [y1 y2].
rewrite last_app; simpl fst.
case (Loc.eq d0 y1).
unfold S1, StateToMove, StateBeing, StateDone.
intros; elim (in_move__in_srcdst (x1, x2) ((s, d) :: t1)); auto; intros.
simpl snd in H4 |-; simpl fst in H3 |-; (split; right; (try in_tac)).
unfold S1, StateToMove, StateBeing, StateDone.
intros; elim (in_move__in_srcdst (x1, x2) ((s, d) :: t1)); auto; intros.
simpl snd in H4 |-; simpl fst in H3 |-; (split; right; (try in_tac)).
intro; elim (in_app_or (StateBeing (stepf S1)) (StateDone (stepf S1)) (x1, x2));
 auto.
simpl stepf.
destruct m as [s d].
destruct m0 as [s0 d0].
case (Loc.eq s d0).
intros e; rewrite <- e; simpl StateBeing.
unfold S1, StateToMove, StateBeing, StateDone.
intros; elim (in_move__in_srcdst (x1, x2) ((s, d) :: ((s0, s) :: b1))); auto;
 simpl; intros.
split; right; (try in_tac).
elim H2; [intros H4; left; (try exact H4) | intros H4; (try clear H2)].
elim H4; [intros H2; right; (try exact H2) | intros H2; (try clear H4)].
assert (In x1 (s0 :: nil)); auto; (try in_tac).
simpl; auto.
right; (try in_tac).
elim H3; [intros H4; left; (try exact H4) | intros H4; (try clear H3)].
elim H4; [intros H3; right; (try exact H3) | intros H3; (try clear H4)].
rewrite <- e; (try in_tac).
assert (In x2 (s :: nil)); [simpl; auto | try in_tac].
right; (try in_tac).
intro; caseEq (split_move t1 d0); intro.
destruct p as [[t2 b2] d2].
simpl StateBeing.
intros.
generalize (in_split_move t1 t2 d2 d0 b2 H1).
intros.
split; right; elim H2; intros.
rewrite H4 in H3; elim (in_move__in_srcdst (x1, x2) t1); auto; intros.
simpl snd in H6 |-; simpl fst in H5 |-; (try in_tac).
unfold S1, StateToMove, StateBeing, StateDone.
simpl getsrc; (try in_tac).
elim (in_move__in_srcdst (x1, x2) ((s0, d0) :: b1)); (auto; intros).
simpl snd in H6 |-; simpl fst in H5 |-; (try in_tac).
unfold S1, StateToMove, StateBeing, StateDone.
simpl.
simpl in H5 |-.
elim H5; [intros H7; (try clear H5); (try exact H7) | intros H7; (try clear H5)].
assert (In x1 (s0 :: nil)); simpl; auto.
right; in_tac.
right; in_tac.
inversion H4.
simpl.
subst b2.
rewrite H4 in H3.
elim (in_move__in_srcdst (x1, x2) t1); (auto; intros).
simpl snd in H7 |-.
right; in_tac.
unfold S1, StateToMove, StateBeing, StateDone.
elim (in_move__in_srcdst (x1, x2) ((s0, d0) :: b1)); auto; intros.
simpl snd in H6 |-; (try in_tac).
apply
 (in_or_app (getdst ((s, d) :: t1)) (getdst ((s0, d0) :: b1) ++ getdst d1) x2);
 right; (try in_tac).
caseEq b1.
intros h1 h2; inversion h2.
intros m l heq.
generalize (app_rewriter _ l m); intros [y [r H2]]; rewrite H2.
destruct y as [y1 y2].
rewrite last_app; simpl fst.
case (Loc.eq d0 y1).
unfold S1, StateToMove, StateBeing, StateDone.
generalize (last_replace r y1 y2).
unfold Move; intros H3 H6.
rewrite H3.
intro.
elim (in_app_or r ((T y1, y2) :: nil) (x1, x2)); auto.
intro.
rewrite heq; rewrite H2; (split; right).
elim (in_move__in_srcdst (x1, x2) r); auto; simpl fst; simpl snd; intros;
 (try in_tac).
simpl.
rewrite getsrc_app; (right; (try in_tac)).
elim (in_move__in_srcdst (x1, x2) r); auto; simpl fst; simpl snd; intros;
 (try in_tac).
simpl.
rewrite getdst_app; right; (try in_tac).
intros h; inversion h; inversion H5.
split; [left; simpl; auto | right].
unfold T; case (Loc.type y1); auto.
subst y2.
rewrite heq; rewrite H2.
simpl.
rewrite getdst_app; simpl.
assert (In x2 (x2 :: nil)); [simpl; auto | right; (try in_tac)].
unfold S1, StateToMove, StateBeing, StateDone.
intro; rewrite heq; rewrite H2; (split; right).
intros; elim (in_move__in_srcdst (x1, x2) (r ++ ((y1, y2) :: nil))); auto;
 intros.
simpl snd in H5 |-; simpl fst in H4 |-.
simpl.
right; (try in_tac).
apply in_or_app; right; simpl; right; (try in_tac).
elim (in_move__in_srcdst (x1, x2) (r ++ ((y1, y2) :: nil))); auto; intros.
simpl snd in H5 |-.
simpl.
right; (try in_tac).
apply in_or_app; right; simpl; right; (try in_tac).
simpl stepf.
destruct m as [s d].
destruct m0 as [s0 d0].
case (Loc.eq s d0).
unfold S1, StateToMove, StateBeing, StateDone.
intros; elim (in_move__in_srcdst (x1, x2) d1); auto; intros.
simpl in H3 |-; simpl in H2 |-.
split; right; (try in_tac).
intro; caseEq (split_move t1 d0); intro.
destruct p as [[t2 b2] d2].
simpl StateDone.
unfold S1, StateToMove, StateBeing, StateDone.
intros; elim (in_move__in_srcdst (x1, x2) d1); auto; intros.
simpl in H3 |-; simpl in H4 |-.
split; right; (try in_tac).
caseEq b1.
unfold S1, StateToMove, StateBeing, StateDone.
intros; elim (in_move__in_srcdst (x1, x2) ((s0, d0) :: d1)); auto; intros.
simpl in H5 |-; simpl in H4 |-; split; right; (try in_tac).
simpl.
elim H4; [intros H6; right; (try exact H6) | intros H6; (try clear H4)].
assert (In x1 (x1 :: nil)); [simpl; auto | rewrite H6; (try in_tac)].
right; (try in_tac).
elim H5; [intros H6; right; simpl; (try exact H6) | intros H6; (try clear H5)].
assert (In x2 (x2 :: nil)); [simpl; auto | rewrite H6; (try in_tac)].
try in_tac.
intros m l heq.
generalize (app_rewriter _ l m); intros [y [r H2]]; rewrite H2.
destruct y as [y1 y2].
rewrite last_app; simpl fst.
case (Loc.eq d0 y1).
unfold S1, StateToMove, StateBeing, StateDone.
unfold S1, StateToMove, StateBeing, StateDone.
intros.
elim H3; intros.
inversion H4.
simpl; split; right; auto.
right; apply in_or_app; right; simpl; auto.
right; apply in_or_app; right; simpl; auto.
elim H4; intros.
inversion H5.
simpl; split; [right | left].
rewrite heq; rewrite H2; simpl.
rewrite <- e; rewrite H7.
rewrite getsrc_app; simpl.
right; assert (In x1 (x1 :: nil)); [simpl; auto | try in_tac].
unfold T; case (Loc.type x1); auto.
elim (in_move__in_srcdst (x1, x2) d1); (auto; intros).
simpl snd in H7 |-; simpl fst in H6 |-; split; right; (try in_tac).
unfold S1, StateToMove, StateBeing, StateDone.
intros; elim (in_move__in_srcdst (x1, x2) ((s0, d0) :: d1));
 (auto; simpl; intros).
split; right.
elim H4; [intros H6; right; (try exact H6) | intros H6; (try clear H4)].
apply in_or_app; right; simpl; auto.
right; (try in_tac).
elim H5; [intros H6; right; (try exact H6) | intros H6; (try clear H5)].
apply in_or_app; right; simpl; auto.
right; (try in_tac).
Qed.
 
Lemma getsrc_f: forall s l, In s (getsrc l) ->  (exists d , In (s, d) l ).
Proof.
induction l; simpl getsrc.
simpl; (intros h; elim h).
intros; destruct a as [a1 a2].
simpl in H |-.
elim H; [intros H0; (try clear H); (try exact H0) | intros H0; (try clear H)].
subst a1.
exists a2; simpl; auto.
simpl.
elim IHl; [intros d H; (try clear IHl); (try exact H) | idtac]; auto.
exists d; [right; (try assumption)].
Qed.
 
Lemma incl_src: forall l1 l2, incl l1 l2 ->  incl (getsrc l1) (getsrc l2).
Proof.
intros.
unfold incl in H |-.
unfold incl.
intros a H0; (try assumption).
generalize (getsrc_f a).
intros H1; elim H1 with ( l := l1 );
 [intros d H2; (try clear H1); (try exact H2) | idtac]; auto.
assert (In (a, d) l2).
apply H; auto.
elim (in_move__in_srcdst (a, d) l2); auto.
Qed.
 
Lemma getdst_f: forall d l, In d (getdst l) ->  (exists s , In (s, d) l ).
Proof.
induction l; simpl getdst.
simpl; (intros h; elim h).
intros; destruct a as [a1 a2].
simpl in H |-.
elim H; [intros H0; (try clear H); (try exact H0) | intros H0; (try clear H)].
subst a2.
exists a1; simpl; auto.
simpl.
elim IHl; [intros s H; (try clear IHl); (try exact H) | idtac]; auto.
exists s; [right; (try assumption)].
Qed.
 
Lemma incl_dst: forall l1 l2, incl l1 l2 ->  incl (getdst l1) (getdst l2).
Proof.
intros.
unfold incl in H |-.
unfold incl.
intros a H0; (try assumption).
generalize (getdst_f a).
intros H1; elim H1 with ( l := l1 );
 [intros d H2; (try clear H1); (try exact H2) | idtac]; auto.
assert (In (d, a) l2).
apply H; auto.
elim (in_move__in_srcdst (d, a) l2); auto.
Qed.
 
Lemma src_tmp2_res:
 forall S1 x1 x2,
 In
  (x1, x2)
  (StateToMove (Pmov S1) ++ (StateBeing (Pmov S1) ++ StateDone (Pmov S1))) ->
  (In x1 temporaries2 \/
   In x1 (getsrc (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1)))) /\
  (In x2 temporaries2 \/
   In x2 (getdst (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1)))).
Proof.
intros S1; elim S1  using (well_founded_ind (Wf_nat.well_founded_ltof _ mesure)).
clear S1; intros S1 Hrec.
destruct S1 as [[t b] d]; set (S1:=(t, b, d)).
unfold S1; rewrite Pmov_equation; intros.
destruct t.
destruct b.
apply srcdst_tmp2_stepf; auto.
elim Hrec with ( y := stepf S1 ) ( x1 := x1 ) ( x2 := x2 );
 [idtac | apply stepf1_dec; auto | auto].
intros.
elim H1; [intros H2; (try clear H1); (try exact H2) | intros H2; (try clear H1)].
elim H0; [intros H1; (try clear H0); (try exact H1) | intros H1; (try clear H0)].
split; [left; (try assumption) | idtac].
left; (try assumption).
elim (getsrc_f x1) with ( 1 := H1 ); intros x3 H3.
split; auto.
elim srcdst_tmp2_stepf with ( 1 := H3 ); auto.
elim H0; [intros H1; (try clear H0); (try exact H1) | intros H1; (try clear H0)].
elim (getdst_f x2) with ( 1 := H2 ); intros x3 H3.
split; auto.
elim srcdst_tmp2_stepf with ( 1 := H3 ); auto.
elim (getsrc_f x1) with ( 1 := H1 ); intros x3 H3.
elim srcdst_tmp2_stepf with ( 1 := H3 ); auto.
clear H3.
elim (getdst_f x2) with ( 1 := H2 ); intros x4 H3.
elim srcdst_tmp2_stepf with ( 1 := H3 ); auto.
elim Hrec with ( y := stepf S1 ) ( x1 := x1 ) ( x2 := x2 );
 [idtac | apply stepf1_dec; auto | auto].
intros.
elim H1; [intros H2; (try clear H1); (try exact H2) | intros H2; (try clear H1)].
elim H0; [intros H1; (try clear H0); (try exact H1) | intros H1; (try clear H0)].
split; [left; (try assumption) | idtac].
left; (try assumption).
elim (getsrc_f x1) with ( 1 := H1 ); intros x3 H3.
split; auto.
elim srcdst_tmp2_stepf with ( 1 := H3 ); auto.
elim H0; [intros H1; (try clear H0); (try exact H1) | intros H1; (try clear H0)].
elim (getdst_f x2) with ( 1 := H2 ); intros x3 H3.
split; auto.
elim srcdst_tmp2_stepf with ( 1 := H3 ); auto.
elim (getsrc_f x1) with ( 1 := H1 ); intros x3 H3.
elim srcdst_tmp2_stepf with ( 1 := H3 ); auto.
clear H3.
elim (getdst_f x2) with ( 1 := H2 ); intros x4 H3.
elim srcdst_tmp2_stepf with ( 1 := H3 ); auto.
Qed.
 
Lemma wt_add_moves:
 forall p b,
 List.map Loc.type (getsrc p) = List.map Loc.type (getdst p) ->
 locs_read_ok (getsrc p) ->
 locs_write_ok (getdst p) ->
 wt_block tf b ->
  wt_block
   tf
   (fold_left
     (fun (k0 : LTL.block) =>
      fun (p0 : loc * loc) => add_move (fst p0) (snd p0) k0) p b).
Proof.
induction p.
intros; simpl; auto.
intros; destruct a as [a1 a2]; simpl.
apply IHp; auto.
inversion H; auto.
simpl in H0 |-.
unfold locs_read_ok in H0 |-.
simpl in H0 |-.
unfold locs_read_ok; auto.
generalize H1; unfold locs_write_ok; simpl; auto.
apply wt_add_move; (try assumption).
simpl in H0 |-.
unfold locs_read_ok in H0 |-.
apply H0.
simpl; left; trivial.
unfold locs_write_ok in H1 |-; apply H1.
simpl; left; trivial.
inversion H; auto.
Qed.
 
Lemma map_f_getsrc_getdst:
 forall (b : Set) (f : Reg ->  b) p,
 map f (getsrc p) = map f (getdst p) ->
 forall x1 x2, In (x1, x2) p ->  f x1 = f x2.
Proof.
intros b f0 p; induction p; simpl; auto.
intros; contradiction.
destruct a.
simpl.
intros heq; injection heq.
intros h1 h2.
intros x1 x2 [H3|H3].
injection H3.
intros; subst; auto.
apply IHp; auto.
Qed.
 
Lemma wt_parallel_move':
 forall p b,
 List.map Loc.type (getsrc p) = List.map Loc.type (getdst p) ->
 locs_read_ok (getsrc p) ->
 locs_write_ok (getdst p) -> wt_block tf b ->  wt_block tf (p_move p b).
Proof.
unfold p_move.
unfold P_move.
intros; apply wt_add_moves; auto.
rewrite getsrc_map; rewrite getdst_map.
rewrite list_map_compose.
rewrite list_map_compose.
apply list_map_exten.
generalize (move_types_res (p, nil, nil)); auto.
destruct x as [x1 x2]; simpl; intros; auto.
symmetry; apply H3.
simpl.
rewrite app_nil.
apply map_f_getsrc_getdst; auto.
in_tac.
unfold locs_read_ok.
intros l H3.
elim getsrc_f with ( 1 := H3 ); intros x3 H4.
elim (src_tmp2_res (p, nil, nil) l x3).
simpl.
rewrite app_nil.
intros [[H'|[H'|H']]|H'] _.
subst l; hnf; auto.
subst l; hnf; auto.
contradiction.
apply H0; auto.
in_tac.
intros l H3.
elim getdst_f with ( 1 := H3 ); intros x3 H4.
elim (src_tmp2_res (p, nil, nil) x3 l).
simpl.
rewrite app_nil.
intros _ [[H'|[H'|H']]|H'].
subst l; hnf; auto.
subst l; hnf; auto.
contradiction.
apply H1; auto.
in_tac.
Qed.
 
Theorem wt_parallel_moveX:
 forall srcs dsts b,
 List.map Loc.type srcs = List.map Loc.type dsts ->
 locs_read_ok srcs ->
 locs_write_ok dsts -> wt_block tf b ->  wt_block tf (parallel_move srcs dsts b).
Proof.
unfold parallel_move, parallel_move_order, P_move.
intros.
generalize (wt_parallel_move' (listsLoc2Moves srcs dsts)); intros H'.
unfold p_move, P_move in H' |-.
apply H'; auto.
elim (getdst_lists2moves srcs dsts); auto.
unfold Allocation.listsLoc2Moves, listsLoc2Moves.
intros heq1 heq2; rewrite heq1; rewrite heq2; auto.
repeat rewrite <- (list_length_map Loc.type).
rewrite H; auto.
elim (getdst_lists2moves srcs dsts); auto.
unfold Allocation.listsLoc2Moves, listsLoc2Moves.
intros heq1 heq2; rewrite heq1; auto.
repeat rewrite <- (list_length_map Loc.type).
rewrite H; auto.
elim (getdst_lists2moves srcs dsts); auto.
unfold Allocation.listsLoc2Moves, listsLoc2Moves.
intros heq1 heq2; rewrite heq2; auto.
repeat rewrite <- (list_length_map Loc.type).
rewrite H; auto.
Qed.
 
End wt_move_correction.

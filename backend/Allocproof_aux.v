(** Correctness results for the [parallel_move] function defined in
  file [Allocation].

  The present file, contributed by Laurence Rideau, glues the general
  results over the parallel move algorithm (see file [Parallelmove])
  with the correctness proof for register allocation (file [Allocproof]).
*)

Require Import Coqlib.
Require Import Values.
Require Import Parallelmove.
Require Import Allocation.
Require Import LTL.
Require Import Locations.
Require Import Conventions.
 
Section parallel_move_correction.
Variable ge : LTL.genv.
Variable sp : val.
Hypothesis
   add_move_correct :
   forall src dst k rs m,
    (exists rs' ,
     exec_instrs ge sp (add_move src dst k) rs m k rs' m /\
     (rs' dst = rs src /\
      (forall l,
       Loc.diff l dst ->
       Loc.diff l (R IT1) -> Loc.diff l (R FT1) ->  rs' l = rs l)) ).
 
Lemma exec_instr_update:
 forall a1 a2 k e m,
  (exists rs' ,
   exec_instrs ge sp (add_move a1 a2 k) e m k rs' m /\
   (rs' a2 = update e a2 (e a1) a2 /\
    (forall l,
     Loc.diff l a2 ->
     Loc.diff l (R IT1) -> Loc.diff l (R FT1) ->  rs' l = (update e a2 (e a1)) l))
   ).
Proof.
intros; destruct (add_move_correct a1 a2 k e m) as [rs' [Hf [R1 R2]]].
exists rs'; (repeat split); auto.
generalize (get_update_id e a2); unfold get, Locmap.get; intros H; rewrite H;
 auto.
intros l H0; generalize (get_update_diff e a2); unfold get, Locmap.get;
 intros H; rewrite H; auto.
apply Loc.diff_sym; assumption.
Qed.
 
Lemma map_inv:
 forall (A B : Set) (f f' : A ->  B) l,
 map f l = map f' l -> forall x, In x l ->  f x = f' x.
Proof.
induction l; simpl; intros Hmap x Hin.
elim Hin.
inversion Hmap.
elim Hin; intros H; [subst a | apply IHl]; auto.
Qed.
 
Fixpoint reswellFormed (p : Moves) : Prop :=
 match p with
   nil => True
  | (s, d) :: l => Loc.notin s (getdst l) /\ reswellFormed l
 end.
 
Definition temporaries1 := R IT1 :: (R FT1 :: nil).
 
Lemma no_overlap_list_pop:
 forall p m, no_overlap_list (m :: p) ->  no_overlap_list p.
Proof.
induction p; unfold no_overlap_list, no_overlap; destruct m as [m1 m2]; simpl;
 auto.
Qed.
 
Lemma exec_instrs_pmov:
 forall p k rs m,
 no_overlap_list p ->
 Loc.disjoint (getdst p) temporaries1 ->
 Loc.disjoint (getsrc p) temporaries1 ->
  (exists rs' ,
   exec_instrs
    ge sp
    (fold_left
      (fun (k0 : block) => fun (p0 : loc * loc) => add_move (fst p0) (snd p0) k0)
      p k) rs m k rs' m /\
   (forall l,
    (forall r, In r (getdst p) ->  r = l \/ Loc.diff r l) ->
    Loc.diff l (Locations.R IT1) ->
    Loc.diff l (Locations.R FT1) ->  rs' l = (sexec p rs) l) ).
Proof.
induction p; intros k rs m.
simpl; exists rs; (repeat split); auto; apply exec_refl.
destruct a as [a1 a2]; simpl; intros Hno_O Hdisd Hdiss;
 elim (IHp (add_move a1 a2 k) rs m);
 [idtac | apply no_overlap_list_pop with (a1, a2) |
  apply (Loc.disjoint_cons_left a2) | apply (Loc.disjoint_cons_left a1)];
 (try assumption).
intros rs' Hexec;
 destruct (add_move_correct a1 a2 k rs' m) as [rs'' [Hexec2 [R1 R2]]].
exists rs''; elim Hexec; intros; (repeat split).
apply exec_trans with ( b2 := add_move a1 a2 k ) ( rs2 := rs' ) ( m2 := m );
 auto.
intros l Heqd Hdi Hdf; case (Loc.eq a2 l); intro.
subst l; generalize get_update_id; unfold get, Locmap.get; intros Hgui;
 rewrite Hgui; rewrite R1.
apply H0; auto.
unfold no_overlap_list, no_overlap in Hno_O |-; simpl in Hno_O |-; intros;
 generalize (Hno_O a1).
intros H8; elim H8 with ( s := r );
 [intros H9; left | intros H9; right; apply Loc.diff_sym | left | right]; auto.
unfold Loc.disjoint in Hdiss |-; apply Hdiss; simpl; left; trivial.
apply Hdiss; simpl; [left | right; left]; auto.
elim (Heqd a2);
 [intros H7; absurd (a2 = l); auto | intros H7; auto | left; trivial].
generalize get_update_diff; unfold get, Locmap.get; intros H6; rewrite H6; auto.
rewrite R2; auto.
apply Loc.diff_sym; auto.
Qed.
 
Definition p_move :=
   fun (l : list (loc * loc)) =>
   fun (k : block) =>
   fold_left
    (fun (k0 : block) => fun (p : loc * loc) => add_move (fst p) (snd p) k0)
    (P_move l) k.
 
Lemma norepet_SD: forall p, Loc.norepet (getdst p) ->  simpleDest p.
Proof.
induction p; (simpl; auto).
destruct a as [a1 a2].
intro; inversion H.
split.
apply notindst_nW; auto.
apply IHp; auto.
Qed.
 
Theorem SDone_stepf:
 forall S1, StateDone (stepf S1) = nil ->  StateDone S1 = nil.
Proof.
destruct S1 as [[t b] d]; destruct t.
destruct b; auto.
destruct m as [m1 m2]; simpl.
destruct b.
simpl; intro; discriminate.
case (Loc.eq m2 (fst (last (m :: b)))); simpl; intros; discriminate.
destruct m as [a1 a2]; simpl.
destruct b.
case (Loc.eq a1 a2); simpl; intros; auto.
destruct m as [m1 m2]; case (Loc.eq a1 m2); intro; (try (simpl; auto; fail)).
case (split_move t m2).
(repeat destruct p); simpl; intros; auto.
destruct b; (try (simpl; intro; discriminate)); auto.
case (Loc.eq m2 (fst (last (m :: b)))); intro; simpl; intro; discriminate.
Qed.
 
Theorem SDone_Pmov: forall S1, StateDone (Pmov S1) = nil ->  StateDone S1 = nil.
Proof.
intros S1; elim S1  using (well_founded_ind (Wf_nat.well_founded_ltof _ mesure)).
clear S1; intros S1; intros Hrec.
destruct S1 as [[t b] d].
rewrite Pmov_equation.
destruct t.
destruct b; auto.
intro; assert (StateDone (stepf (nil, m :: b, d)) = nil);
 [apply Hrec; auto; apply stepf1_dec | apply SDone_stepf]; auto.
intro; assert (StateDone (stepf (m :: t, b, d)) = nil);
 [apply Hrec; auto; apply stepf1_dec | apply SDone_stepf]; auto.
Qed.
 
Lemma no_overlap_temp: forall r s, In s temporaries ->  r = s \/ Loc.diff r s.
Proof.
intros r s H; case (Loc.eq r s); intros e; [left | right]; (try assumption).
unfold Loc.diff; destruct r.
destruct s; trivial.
red; intro; elim e; rewrite H0; auto.
destruct s0; destruct s; trivial;
 (elim H; [intros H1 | intros [H1|[H1|[H1|[H1|[H1|H1]]]]]]; (try discriminate);
   inversion H1).
Qed.
 
Lemma getsrcdst_app:
 forall l1 l2,
 getdst l1 ++ getdst l2 = getsrc l1 ++ getsrc l2 ->
  getdst l1 = getsrc l1 /\ getdst l2 = getsrc l2.
Proof.
induction l1; simpl; auto.
destruct a as [a1 a2]; intros; inversion H.
subst a1; inversion H;
 (elim IHl1 with ( l2 := l2 );
   [intros H0 H3; (try clear IHl1); (try exact H0) | idtac]; auto).
rewrite H0; auto.
Qed.
 
Lemma In_norepet:
 forall r x l, Loc.norepet l -> In x l -> In r l ->  r = x \/ Loc.diff r x.
Proof.
induction l; simpl; intros.
elim H1.
inversion H.
subst hd.
elim H1; intros H2; clear H1; elim H0; intros H1.
rewrite <- H1; rewrite <- H2; auto.
subst a; right; apply Loc.in_notin_diff with l; auto.
subst a; right; apply Loc.diff_sym; apply Loc.in_notin_diff with l; auto.
apply IHl; auto.
Qed.
 
Definition no_overlap_stateD (S : State) :=
   no_overlap
    (getsrc (StateToMove S ++ (StateBeing S ++ StateDone S)))
    (getdst (StateToMove S ++ (StateBeing S ++ StateDone S))).
 
Ltac
incl_tac_rec :=
(auto with datatypes; fail)
 ||
   (apply in_cons; incl_tac_rec)
    ||
      (apply in_or_app; left; incl_tac_rec)
       ||
         (apply in_or_app; right; incl_tac_rec)
          ||
            (apply incl_appl; incl_tac_rec) ||
             (apply incl_appr; incl_tac_rec) || (apply incl_tl; incl_tac_rec).
 
Ltac incl_tac := (repeat (apply incl_cons || apply incl_app)); incl_tac_rec.
 
Ltac
in_tac :=
match goal with
| |- In ?x ?L1 =>
match goal with
| H:In x ?L2 |- _ =>
let H1 := fresh "H" in
(assert (H1: incl L2 L1); [incl_tac | apply (H1 x)]); auto; fail
| _ => fail end end.
 
Lemma in_cons_noteq:
 forall (A : Set) (a b : A) (l : list A), In a (b :: l) -> a <> b ->  In a l.
Proof.
intros A a b l; simpl; intros.
elim H; intros H1; (try assumption).
absurd (a = b); auto.
Qed.
 
Lemma no_overlapD_inv:
 forall S1 S2, step S1 S2 -> no_overlap_stateD S1 ->  no_overlap_stateD S2.
Proof.
intros S1 S2 STEP; inversion STEP; unfold no_overlap_stateD, no_overlap; simpl;
 auto; (repeat (rewrite getsrc_app; rewrite getdst_app; simpl)); intros.
apply H1; in_tac.
destruct m as [m1 m2]; apply H1; in_tac.
apply H1; in_tac.
case (Loc.eq r (T r0)); intros e.
elim (no_overlap_temp s0 r);
 [intro; left; auto | intro; right; apply Loc.diff_sym; auto | unfold T in e |-].
destruct (Loc.type r0); simpl; [right; left | right; right; right; right; left];
 auto.
case (Loc.eq s0 (T r0)); intros es.
apply (no_overlap_temp r s0); unfold T in es |-; destruct (Loc.type r0); simpl;
 [right; left | right; right; right; right; left]; auto.
apply H1; apply in_cons_noteq with ( b := T r0 ); auto; in_tac.
apply H3; in_tac.
Qed.
 
Lemma no_overlapD_invpp:
 forall S1 S2, stepp S1 S2 -> no_overlap_stateD S1 ->  no_overlap_stateD S2.
Proof.
intros; induction H as [r|r1 r2 r3 H H1 HrecH]; auto.
apply HrecH; auto.
apply no_overlapD_inv with r1; auto.
Qed.
 
Lemma no_overlapD_invf:
 forall S1, stepInv S1 -> no_overlap_stateD S1 ->  no_overlap_stateD (stepf S1).
Proof.
intros; destruct S1 as [[t1 b1] d1].
destruct t1; destruct b1; auto.
set (S1:=(nil (A:=Move), m :: b1, d1)).
apply (no_overlapD_invpp S1); [apply dstep_step; auto | assumption].
apply f2ind; [unfold S1 | idtac | idtac]; auto.
generalize H0; clear H0; unfold no_overlap_stateD; destruct m as [m1 m2].
intros; apply no_overlap_noOverlap.
unfold no_overlap_state; simpl.
generalize H0; clear H0; unfold no_overlap; (repeat rewrite getdst_app);
 (repeat rewrite getsrc_app); simpl; intros.
apply H0.
elim H1; intros H4; [left; assumption | right; in_tac].
elim H2; intros H4; [left; assumption | right; in_tac].
set (S1:=(m :: t1, nil (A:=Move), d1)).
apply (no_overlapD_invpp S1); [apply dstep_step; auto | assumption].
apply f2ind; [unfold S1 | idtac | idtac]; auto.
generalize H0; clear H0; unfold no_overlap_stateD; destruct m as [m1 m2].
intros; apply no_overlap_noOverlap.
unfold no_overlap_state; simpl.
generalize H0; clear H0; unfold no_overlap; (repeat rewrite getdst_app);
 (repeat rewrite getsrc_app); simpl; (repeat rewrite app_nil); intros.
apply H0.
elim H1; intros H4; [left; assumption | right; (try in_tac)].
elim H2; intros H4; [left; assumption | right; in_tac].
set (S1:=(m :: t1, m0 :: b1, d1)).
apply (no_overlapD_invpp S1); [apply dstep_step; auto | assumption].
apply f2ind; [unfold S1 | idtac | idtac]; auto.
generalize H0; clear H0; unfold no_overlap_stateD; destruct m as [m1 m2].
intros; apply no_overlap_noOverlap.
unfold no_overlap_state; simpl.
generalize H0; clear H0; unfold no_overlap; (repeat rewrite getdst_app);
 (repeat rewrite getsrc_app); destruct m0; simpl; intros.
apply H0.
elim H1; intros H4; [left; assumption | right; in_tac].
elim H2; intros H4; [left; assumption | right; in_tac].
Qed.
 
Lemma no_overlapD_res:
 forall S1, stepInv S1 -> no_overlap_stateD S1 ->  no_overlap_stateD (Pmov S1).
Proof.
intros S1; elim S1  using (well_founded_ind (Wf_nat.well_founded_ltof _ mesure)).
clear S1; intros S1 Hrec.
destruct S1 as [[t b] d].
rewrite Pmov_equation.
destruct t; auto.
destruct b; auto.
intros; apply Hrec.
apply stepf1_dec; auto.
apply (dstep_inv (nil, m :: b, d)); auto.
apply f2ind'; auto.
apply no_overlap_noOverlap.
generalize H0; unfold no_overlap_stateD, no_overlap_state, no_overlap; simpl.
destruct m; (repeat rewrite getdst_app); (repeat rewrite getsrc_app).
intros H1 r1 H2 s H3; (try assumption).
apply H1; in_tac.
apply no_overlapD_invf; auto.
intros; apply Hrec.
apply stepf1_dec; auto.
apply (dstep_inv (m :: t, b, d)); auto.
apply f2ind'; auto.
apply no_overlap_noOverlap.
generalize H0; destruct m;
 unfold no_overlap_stateD, no_overlap_state, no_overlap; simpl;
 (repeat (rewrite getdst_app; simpl)); (repeat (rewrite getsrc_app; simpl)).
simpl; intros H1 r1 H2 s H3; (try assumption).
apply H1.
elim H2; intros H4; [left; (try assumption) | right; in_tac].
elim H3; intros H4; [left; (try assumption) | right; in_tac].
apply no_overlapD_invf; auto.
Qed.
 
Definition temporaries1_3 := R IT1 :: (R FT1 :: (R IT3 :: nil)).
 
Definition temporaries2 := R IT2 :: (R FT2 :: nil).
 
Definition no_tmp13_state (S1 : State) :=
   Loc.disjoint (getsrc (StateDone S1)) temporaries1_3 /\
   Loc.disjoint (getdst (StateDone S1)) temporaries1_3.
 
Definition Done_well_formed (S1 S2 : State) :=
   forall x,
    (In x (getsrc (StateDone S2)) ->
      In x temporaries2 \/ In x (getsrc (StateToMove S1 ++ StateBeing S1))) /\
    (In x (getdst (StateDone S2)) ->
      In x temporaries2 \/ In x (getdst (StateToMove S1 ++ StateBeing S1))).
 
Lemma Done_notmp3_inv:
 forall S1 S2,
 step S1 S2 ->
 (forall x,
  In x (getdst (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1))) ->
   Loc.diff x (R IT3)) ->
 forall x,
 In x (getdst (StateToMove S2 ++ (StateBeing S2 ++ StateDone S2))) ->
  Loc.diff x (R IT3).
Proof.
intros S1 S2 STEP; inversion STEP; (try (simpl; trivial; fail));
 simpl StateDone; simpl StateToMove; simpl StateBeing; simpl getdst;
 (repeat (rewrite getdst_app; simpl)); intros.
apply H1; in_tac.
destruct m; apply H1; in_tac.
apply H1; in_tac.
case (Loc.eq x (T r0)); intros e.
unfold T in e |-; destruct (Loc.type r0); rewrite e; simpl; red; intro;
 discriminate.
apply H1; apply in_cons_noteq with ( b := T r0 ); auto; in_tac.
apply H3; in_tac.
Qed.
 
Lemma Done_notmp3_invpp:
 forall S1 S2,
 stepp S1 S2 ->
 (forall x,
  In x (getdst (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1))) ->
   Loc.diff x (R IT3)) ->
 forall x,
 In x (getdst (StateToMove S2 ++ (StateBeing S2 ++ StateDone S2))) ->
  Loc.diff x (R IT3).
Proof.
intros S1 S2 H H0; (try assumption).
induction H as [r|r1 r2 r3 H1 H2 Hrec]; auto.
apply Hrec; auto.
apply Done_notmp3_inv with r1; auto.
Qed.
 
Lemma Done_notmp3_invf:
 forall S1,
 stepInv S1 ->
 (forall x,
  In x (getdst (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1))) ->
   Loc.diff x (R IT3)) ->
 forall x,
 In
  x
  (getdst
    (StateToMove (stepf S1) ++ (StateBeing (stepf S1) ++ StateDone (stepf S1)))) ->
  Loc.diff x (R IT3).
Proof.
intros S1 H H0; (try assumption).
generalize H; unfold stepInv; intros [Hpath [HSD [HnoO [Hnotmp HnotmpL]]]].
destruct S1 as [[t1 b1] d1]; set (S1:=(t1, b1, d1)); destruct t1; destruct b1;
 auto; apply (Done_notmp3_invpp S1); auto; apply dstep_step; auto; apply f2ind;
 unfold S1; auto.
Qed.
 
Lemma Done_notmp3_res:
 forall S1,
 stepInv S1 ->
 (forall x,
  In x (getdst (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1))) ->
   Loc.diff x (R IT3)) ->
 forall x,
 In
  x
  (getdst
    (StateToMove (Pmov S1) ++ (StateBeing (Pmov S1) ++ StateDone (Pmov S1)))) ->
  Loc.diff x (R IT3).
Proof.
intros S1; elim S1  using (well_founded_ind (Wf_nat.well_founded_ltof _ mesure)).
clear S1; intros S1 Hrec.
destruct S1 as [[t b] d]; set (S1:=(t, b, d)).
unfold S1; rewrite Pmov_equation.
intros H; generalize H; intros [Hpath [HSD [HnoO [Htmp HtmpL]]]].
destruct t; [destruct b; auto | idtac];
 (intro; apply Hrec;
   [apply stepf1_dec | apply (dstep_inv S1); auto; apply f2ind'
    | apply Done_notmp3_invf]; auto).
Qed.
 
Lemma Done_notmp1_inv:
 forall S1 S2,
 step S1 S2 ->
 (forall x,
  In x (getdst (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1))) ->
   Loc.diff x (R IT1) /\ Loc.diff x (R FT1)) ->
 forall x,
 In x (getdst (StateToMove S2 ++ (StateBeing S2 ++ StateDone S2))) ->
  Loc.diff x (R IT1) /\ Loc.diff x (R FT1).
Proof.
intros S1 S2 STEP; inversion STEP; (try (simpl; trivial; fail));
 (repeat (rewrite getdst_app; simpl)); intros.
apply H1; in_tac.
destruct m; apply H1; in_tac.
apply H1; in_tac.
case (Loc.eq x (T r0)); intro.
rewrite e; unfold T; case (Loc.type r0); simpl; split; red; intro; discriminate.
apply H1; apply in_cons_noteq with ( b := T r0 ); (try assumption); in_tac.
apply H3; in_tac.
Qed.
 
Lemma Done_notmp1_invpp:
 forall S1 S2,
 stepp S1 S2 ->
 (forall x,
  In x (getdst (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1))) ->
   Loc.diff x (R IT1) /\ Loc.diff x (R FT1)) ->
 forall x,
 In x (getdst (StateToMove S2 ++ (StateBeing S2 ++ StateDone S2))) ->
  Loc.diff x (R IT1) /\ Loc.diff x (R FT1).
Proof.
intros S1 S2 H H0; (try assumption).
induction H as [r|r1 r2 r3 H1 H2 Hrec]; auto.
apply Hrec; auto.
apply Done_notmp1_inv with r1; auto.
Qed.
 
Lemma Done_notmp1_invf:
 forall S1,
 stepInv S1 ->
 (forall x,
  In x (getdst (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1))) ->
   Loc.diff x (R IT1) /\ Loc.diff x (R FT1)) ->
 forall x,
 In
  x
  (getdst
    (StateToMove (stepf S1) ++ (StateBeing (stepf S1) ++ StateDone (stepf S1)))) ->
  Loc.diff x (R IT1) /\ Loc.diff x (R FT1).
Proof.
intros S1 H H0; (try assumption).
generalize H; unfold stepInv; intros [Hpath [HSD [HnoO [Hnotmp HnotmpL]]]].
destruct S1 as [[t1 b1] d1]; set (S1:=(t1, b1, d1)); destruct t1; destruct b1;
 auto; apply (Done_notmp1_invpp S1); auto; apply dstep_step; auto; apply f2ind;
 unfold S1; auto.
Qed.
 
Lemma Done_notmp1_res:
 forall S1,
 stepInv S1 ->
 (forall x,
  In x (getdst (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1))) ->
   Loc.diff x (R IT1) /\ Loc.diff x (R FT1)) ->
 forall x,
 In
  x
  (getdst
    (StateToMove (Pmov S1) ++ (StateBeing (Pmov S1) ++ StateDone (Pmov S1)))) ->
  Loc.diff x (R IT1) /\ Loc.diff x (R FT1).
Proof.
intros S1; elim S1  using (well_founded_ind (Wf_nat.well_founded_ltof _ mesure)).
clear S1; intros S1 Hrec.
destruct S1 as [[t b] d]; set (S1:=(t, b, d)).
intros H; generalize H; intros [Hpath [HSD [HnoO [Htmp HtmpL]]]].
unfold S1; rewrite Pmov_equation.
destruct t; [destruct b; auto | idtac];
 (intro; apply Hrec;
   [apply stepf1_dec | apply (dstep_inv S1); auto; apply f2ind'
    | apply Done_notmp1_invf]; auto).
Qed.
 
Lemma Done_notmp1src_inv:
 forall S1 S2,
 step S1 S2 ->
 (forall x,
  In x (getsrc (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1))) ->
   Loc.diff x (R IT1) /\ Loc.diff x (R FT1)) ->
 forall x,
 In x (getsrc (StateToMove S2 ++ (StateBeing S2 ++ StateDone S2))) ->
  Loc.diff x (R IT1) /\ Loc.diff x (R FT1).
Proof.
intros S1 S2 STEP; inversion STEP; (try (simpl; trivial; fail));
 (repeat (rewrite getsrc_app; simpl)); intros.
apply H1; in_tac.
destruct m; apply H1; in_tac.
apply H1; in_tac.
case (Loc.eq x (T r0)); intro.
rewrite e; unfold T; case (Loc.type r0); simpl; split; red; intro; discriminate.
apply H1; apply in_cons_noteq with ( b := T r0 ); (try assumption); in_tac.
apply H3; in_tac.
Qed.
 
Lemma Done_notmp1src_invpp:
 forall S1 S2,
 stepp S1 S2 ->
 (forall x,
  In x (getsrc (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1))) ->
   Loc.diff x (R IT1) /\ Loc.diff x (R FT1)) ->
 forall x,
 In x (getsrc (StateToMove S2 ++ (StateBeing S2 ++ StateDone S2))) ->
  Loc.diff x (R IT1) /\ Loc.diff x (R FT1).
Proof.
intros S1 S2 H H0; (try assumption).
induction H as [r|r1 r2 r3 H1 H2 Hrec]; auto.
apply Hrec; auto.
apply Done_notmp1src_inv with r1; auto.
Qed.
 
Lemma Done_notmp1src_invf:
 forall S1,
 stepInv S1 ->
 (forall x,
  In x (getsrc (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1))) ->
   Loc.diff x (R IT1) /\ Loc.diff x (R FT1)) ->
 forall x,
 In
  x
  (getsrc
    (StateToMove (stepf S1) ++ (StateBeing (stepf S1) ++ StateDone (stepf S1)))) ->
  Loc.diff x (R IT1) /\ Loc.diff x (R FT1).
Proof.
intros S1 H H0.
generalize H; unfold stepInv; intros [Hpath [HSD [HnoO [Hnotmp HnotmpL]]]].
destruct S1 as [[t1 b1] d1]; set (S1:=(t1, b1, d1)); destruct t1; destruct b1;
 auto; apply (Done_notmp1src_invpp S1); auto; apply dstep_step; auto;
 apply f2ind; unfold S1; auto.
Qed.
 
Lemma Done_notmp1src_res:
 forall S1,
 stepInv S1 ->
 (forall x,
  In x (getsrc (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1))) ->
   Loc.diff x (R IT1) /\ Loc.diff x (R FT1)) ->
 forall x,
 In
  x
  (getsrc
    (StateToMove (Pmov S1) ++ (StateBeing (Pmov S1) ++ StateDone (Pmov S1)))) ->
  Loc.diff x (R IT1) /\ Loc.diff x (R FT1).
Proof.
intros S1; elim S1  using (well_founded_ind (Wf_nat.well_founded_ltof _ mesure)).
clear S1; intros S1 Hrec.
destruct S1 as [[t b] d]; set (S1:=(t, b, d)).
intros H; generalize H; intros [Hpath [HSD [HnoO [Htmp HtmpL]]]].
unfold S1; rewrite Pmov_equation.
destruct t; [destruct b; auto | idtac];
 (intro; apply Hrec;
   [apply stepf1_dec | apply (dstep_inv S1); auto; apply f2ind'
    | apply Done_notmp1src_invf]; auto).
Qed.
 
Lemma dst_tmp2_step:
 forall S1 S2,
 step S1 S2 ->
 forall x,
 In x (getdst (StateToMove S2 ++ (StateBeing S2 ++ StateDone S2))) ->
  In x temporaries2 \/
  In x (getdst (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1))).
Proof.
intros S1 S2 STEP; inversion STEP; (repeat (rewrite getdst_app; simpl)); intros;
 (try (right; in_tac)).
destruct m; right; in_tac.
case (Loc.eq x (T r0)); intro.
rewrite e; unfold T; case (Loc.type r0); left; [left | right; left]; trivial.
right; apply in_cons_noteq with ( b := T r0 ); auto; in_tac.
Qed.
 
Lemma dst_tmp2_stepp:
 forall S1 S2,
 stepp S1 S2 ->
 forall x,
 In x (getdst (StateToMove S2 ++ (StateBeing S2 ++ StateDone S2))) ->
  In x temporaries2 \/
  In x (getdst (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1))).
Proof.
intros S1 S2 H.
induction H as [r|r1 r2 r3 H1 H2 Hrec]; auto.
intros.
elim Hrec with ( x := x );
 [intros H0; (try clear Hrec); (try exact H0) | intros H0; (try clear Hrec)
  | try clear Hrec]; auto.
generalize (dst_tmp2_step r1 r2); auto.
Qed.
 
Lemma dst_tmp2_stepf:
 forall S1,
 stepInv S1 ->
 forall x,
 In
  x
  (getdst
    (StateToMove (stepf S1) ++ (StateBeing (stepf S1) ++ StateDone (stepf S1)))) ->
  In x temporaries2 \/
  In x (getdst (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1))).
Proof.
intros S1 H H0.
generalize H; unfold stepInv; intros [Hpath [HSD [HnoO [Hnotmp HnotmpL]]]].
destruct S1 as [[t1 b1] d1]; set (S1:=(t1, b1, d1)); destruct t1; destruct b1;
 auto; apply (dst_tmp2_stepp S1); auto; apply dstep_step; auto; apply f2ind;
 unfold S1; auto.
Qed.
 
Lemma dst_tmp2_res:
 forall S1,
 stepInv S1 ->
 forall x,
 In
  x
  (getdst
    (StateToMove (Pmov S1) ++ (StateBeing (Pmov S1) ++ StateDone (Pmov S1)))) ->
  In x temporaries2 \/
  In x (getdst (StateToMove S1 ++ (StateBeing S1 ++ StateDone S1))).
Proof.
intros S1; elim S1  using (well_founded_ind (Wf_nat.well_founded_ltof _ mesure)).
clear S1; intros S1 Hrec.
destruct S1 as [[t b] d]; set (S1:=(t, b, d)).
intros H; generalize H; intros [Hpath [HSD [HnoO [Htmp HtmpL]]]].
unfold S1; rewrite Pmov_equation; intros.
destruct t; auto.
destruct b; auto.
elim Hrec with ( y := stepf S1 ) ( x := x );
 [intros H1 | intros H1 | try clear Hrec | try clear Hrec | try assumption].
left; (try assumption).
apply dst_tmp2_stepf; auto.
apply stepf1_dec; auto.
apply (dstep_inv S1); auto; unfold S1; apply f2ind'; auto.
elim Hrec with ( y := stepf S1 ) ( x := x );
 [intro; left; (try assumption) | intros H1; apply dst_tmp2_stepf; auto |
  apply stepf1_dec; auto |
  apply (dstep_inv S1); auto; unfold S1; apply f2ind'; auto | try assumption].
Qed.
 
Lemma getdst_lists2moves:
 forall srcs dsts,
 length srcs = length dsts ->
  getsrc (listsLoc2Moves srcs dsts) = srcs /\
  getdst (listsLoc2Moves srcs dsts) = dsts.
Proof.
induction srcs; intros dsts; destruct dsts; simpl; auto; intro;
 (try discriminate).
inversion H.
elim IHsrcs with ( dsts := dsts ); auto; intros.
rewrite H2; rewrite H0; auto.
Qed.
 
Lemma stepInv_pnilnil:
 forall p,
 simpleDest p ->
 Loc.disjoint (getsrc p) temporaries ->
 Loc.disjoint (getdst p) temporaries ->
 no_overlap_list p ->  stepInv (p, nil, nil).
Proof.
unfold stepInv; simpl; (repeat split); auto.
rewrite app_nil; auto.
generalize (no_overlap_noOverlap (p, nil, nil)).
simpl; (intros H3; apply H3).
generalize H2; unfold no_overlap_state, no_overlap_list; simpl; intro.
rewrite app_nil; auto.
apply disjoint_tmp__noTmp; auto.
Qed.
 
Lemma noO_list_pnilnil:
 forall (p : Moves),
 simpleDest p ->
 Loc.disjoint (getsrc p) temporaries ->
 Loc.disjoint (getdst p) temporaries ->
 no_overlap_list p ->  no_overlap_list (StateDone (Pmov (p, nil, nil))).
Proof.
intros; generalize (no_overlapD_res (p, nil, nil));
 unfold no_overlap_stateD, no_overlap_list.
rewrite STM_Pmov; rewrite SB_Pmov; simpl; rewrite app_nil; intro.
apply H3; auto.
apply stepInv_pnilnil; auto.
Qed.
 
Lemma dis_srctmp1_pnilnil:
 forall (p : Moves),
 simpleDest p ->
 Loc.disjoint (getsrc p) temporaries ->
 Loc.disjoint (getdst p) temporaries ->
 no_overlap_list p ->
  Loc.disjoint (getsrc (StateDone (Pmov (p, nil, nil)))) temporaries1.
Proof.
intros; generalize (Done_notmp1src_res (p, nil, nil)); simpl.
rewrite STM_Pmov; rewrite SB_Pmov; simpl; rewrite app_nil; intro.
unfold temporaries1.
apply Loc.notin_disjoint; auto.
simpl; intros.
assert (HsI: stepInv (p, nil, nil)); (try apply stepInv_pnilnil); auto.
elim H3 with x; (try assumption).
intros; (repeat split); auto.
intros; split;
 (apply Loc.in_notin_diff with ( ll := temporaries );
   [apply Loc.disjoint_notin with (getsrc p) | simpl]; auto).
Qed.
 
Lemma dis_dsttmp1_pnilnil:
 forall (p : Moves),
 simpleDest p ->
 Loc.disjoint (getsrc p) temporaries ->
 Loc.disjoint (getdst p) temporaries ->
 no_overlap_list p ->
  Loc.disjoint (getdst (StateDone (Pmov (p, nil, nil)))) temporaries1.
Proof.
intros; generalize (Done_notmp1_res (p, nil, nil)); simpl.
rewrite STM_Pmov; rewrite SB_Pmov; simpl; rewrite app_nil; intro.
unfold temporaries1.
apply Loc.notin_disjoint; auto.
simpl; intros.
assert (HsI: stepInv (p, nil, nil)); (try apply stepInv_pnilnil); auto.
elim H3 with x; (try assumption).
intros; (repeat split); auto.
intros; split;
 (apply Loc.in_notin_diff with ( ll := temporaries );
   [apply Loc.disjoint_notin with (getdst p) | simpl]; auto).
Qed.
 
Lemma parallel_move_correct':
 forall p k rs m,
 Loc.norepet (getdst p) ->
 no_overlap_list p ->
 Loc.disjoint (getsrc p) temporaries ->
 Loc.disjoint (getdst p) temporaries ->
  (exists rs' ,
   exec_instrs ge sp (p_move p k) rs m k rs' m /\
   (List.map rs' (getdst p) = List.map rs (getsrc p) /\
    (rs' (R IT3) = rs (R IT3) /\
     (forall l,
      Loc.notin l (getdst p) -> Loc.notin l temporaries ->  rs' l = rs l)))
   ).
Proof.
unfold p_move, P_move.
intros p k rs m Hnorepet HnoOverlap Hdisjointsrc Hdisjointdst.
assert (HsD: simpleDest p); (try (apply norepet_SD; assumption)).
assert (HsI: stepInv (p, nil, nil)); (try (apply stepInv_pnilnil; assumption)).
generalize HsI; unfold stepInv; simpl StateToMove; simpl StateBeing;
 (repeat rewrite app_nil); intros [_ [_ [HnoO [Hnotmp _]]]].
elim (exec_instrs_pmov (StateDone (Pmov (p, nil, nil))) k rs m); auto;
 (try apply noO_list_pnilnil); (try apply dis_dsttmp1_pnilnil);
 (try apply dis_srctmp1_pnilnil); auto.
intros rs' [Hexec R]; exists rs'; (repeat split); auto.
rewrite <- (Fpmov_correct_map p rs); auto.
apply list_map_exten; intros; rewrite <- R; auto;
 (try
   (apply Loc.in_notin_diff with ( ll := temporaries );
     [apply Loc.disjoint_notin with (getdst p) | simpl]; auto)).
generalize (dst_tmp2_res (p, nil, nil)); intros.
elim H0 with ( x := r );
 [intros H2; right |
  simpl; rewrite app_nil; intros H2; apply In_norepet with (getdst p); auto |
  try assumption | rewrite STM_Pmov; rewrite SB_Pmov; auto].
apply Loc.diff_sym; apply Loc.in_notin_diff with ( ll := temporaries );
 (try assumption).
apply Loc.disjoint_notin with (getdst p); auto.
generalize H2; unfold temporaries, temporaries2; intros; in_tac.
rewrite <- (Fpmov_correct_IT3 p rs); auto; rewrite <- R;
 (try (simpl; intro; discriminate)); auto.
intros r H; right; apply (Done_notmp3_res (p, nil, nil)); auto;
 (try (rewrite STM_Pmov; rewrite SB_Pmov; auto)).
simpl; rewrite app_nil; intros; apply Loc.in_notin_diff with temporaries; auto.
apply Loc.disjoint_notin with (getdst p); auto.
simpl; right; right; left; trivial.
intros; rewrite <- (Fpmov_correct_ext p rs); auto; rewrite <- R; auto;
 (try (apply Loc.in_notin_diff with temporaries; simpl; auto)).
intros r H1; right; generalize (dst_tmp2_res (p, nil, nil)); intros.
elim H2 with ( x := r );
 [intros H3 | simpl; rewrite app_nil; intros H3 | assumption
  | rewrite STM_Pmov; rewrite SB_Pmov; auto].
apply Loc.diff_sym; apply Loc.in_notin_diff with temporaries; auto.
generalize H3; unfold temporaries, temporaries2; intros; in_tac.
apply Loc.diff_sym; apply Loc.in_notin_diff with ( ll := getdst p ); auto.
Qed.
 
Lemma parallel_move_correctX:
 forall srcs dsts k rs m,
 List.length srcs = List.length dsts ->
 no_overlap srcs dsts ->
 Loc.norepet dsts ->
 Loc.disjoint srcs temporaries ->
 Loc.disjoint dsts temporaries ->
  (exists rs' ,
   exec_instrs ge sp (parallel_move srcs dsts k) rs m k rs' m /\
   (List.map rs' dsts = List.map rs srcs /\
    (rs' (R IT3) = rs (R IT3) /\
     (forall l, Loc.notin l dsts -> Loc.notin l temporaries ->  rs' l = rs l))) ).
Proof.
intros; unfold parallel_move, parallel_move_order;
 generalize (parallel_move_correct' (listsLoc2Moves srcs dsts) k rs m).
elim (getdst_lists2moves srcs dsts); auto.
intros heq1 heq2; rewrite heq1; rewrite heq2; unfold p_move.
intros H4; apply H4; auto.
unfold no_overlap_list; rewrite heq1; rewrite heq2; auto.
Qed.
 
End parallel_move_correction.

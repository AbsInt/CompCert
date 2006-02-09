(** Translation of parallel moves into sequences of individual moves *)

(** The ``parallel move'' problem, also known as ``parallel assignment'',
  is the following.  We are given a list of (source, destination) pairs
  of locations.  The goal is to find a sequence of elementary
  moves ([loc <- loc] assignments) such that, at the end of the sequence,
  location [dst] contains the value of location [src] at the beginning of
  the sequence, for each ([src], [dst]) pairs in the given problem.
  Moreover, other locations should keep their values, except one register
  of each type, which can be used as temporaries in the generated sequences.

  The parallel move problem is trivial if the sources and destinations do
  not overlap.  For instance,
<<
  (R1, R2) <- (R3, R4)     becomes    R1 <- R3; R2 <- R4
>>
  However, arbitrary overlap is allowed between sources and destinations.
  This requires some care in ordering the individual moves, as in
<<
  (R1, R2) <- (R3, R1)     becomes    R2 <- R1; R1 <- R3
>>
  Worse, cycles (permutations) can require the use of temporaries, as in
<<
  (R1, R2, R3) <- (R2, R3, R1)   becomes   T <- R1; R1 <- R2; R2 <- R3; R3 <- T;
>>
  An amazing fact is that for any parallel move problem, at most one temporary
  (or in our case one integer temporary and one float temporary) is needed.

  The development in this section was contributed by Laurence Rideau and
  Bernard Serpette.  It is described in their paper
  ``Coq à la conquête des moulins'', JFLA 2005, 
  #<A HREF="http://www-sop.inria.fr/lemme/Laurence.Rideau/RideauSerpetteJFLA05.ps">#
  http://www-sop.inria.fr/lemme/Laurence.Rideau/RideauSerpetteJFLA05.ps
  #</A>#
*)

Require Omega.
Require Import Wf_nat.
Require Import Conventions.
Require Import Coqlib.
Require Import Bool_nat.
Require Import TheoryList.
Require Import Bool.
Require Import Arith.
Require Import Peano_dec.
Require Import EqNat.
Require Import Values.
Require Import LTL.
Require Import EqNat.
Require Import Locations.
Require Import AST.
 
Section pmov.
 
Ltac caseEq name := generalize (refl_equal name); pattern name at -1; case name.
Hint Resolve beq_nat_eq .
 
Lemma neq_is_neq: forall (x y : nat), x <> y ->  beq_nat x y = false.
Proof.
unfold not; intros.
caseEq (beq_nat x y); auto.
intro.
elim H; auto.
Qed.
Hint Resolve neq_is_neq .
 
Lemma app_nil: forall (A : Set) (l : list A),  l ++ nil = l.
Proof.
intros A l; induction l as [|a l Hrecl]; auto; simpl; rewrite Hrecl; auto.
Qed.
 
Lemma app_cons:
 forall (A : Set) (l1 l2 : list A) (a : A),  (a :: l1) ++ l2 = a :: (l1 ++ l2).
Proof.
auto.
Qed.
 
Lemma app_app:
 forall (A : Set) (l1 l2 l3 : list A),  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
intros A l1; induction l1 as [|a l1 Hrecl1]; simpl; auto; intros;
 rewrite Hrecl1; auto.
Qed.
 
Lemma app_rewrite:
 forall (A : Set) (l : list A) (x : A),
  (exists y : A , exists r : list A , l ++ (x :: nil) = y :: r  ).
Proof.
intros A l x; induction l as [|a l Hrecl].
exists x; exists (nil (A:=A)); auto.
inversion Hrecl; inversion H.
exists a; exists (l ++ (x :: nil)); auto.
Qed.
 
Lemma app_rewrite2:
 forall (A : Set) (l l2 : list A) (x : A),
  (exists y : A , exists r : list A , l ++ (x :: l2) = y :: r  ).
Proof.
intros A l l2 x; induction l as [|a l Hrecl].
exists x; exists l2; auto.
inversion Hrecl; inversion H.
exists a; exists (l ++ (x :: l2)); auto.
Qed.
 
Lemma app_rewriter:
 forall (A : Set) (l : list A) (x : A),
  (exists y : A , exists r : list A , x :: l = r ++ (y :: nil)  ).
Proof.
intros A l x; induction l as [|a l Hrecl].
exists x; exists (nil (A:=A)); auto.
inversion Hrecl; inversion H.
generalize H0; case x1; simpl; intros; inversion H1.
exists a; exists (x0 :: nil); simpl; auto.
exists x0; exists (a0 :: (a :: l0)); simpl; auto.
Qed.
Hint Resolve app_rewriter .
 
Definition Reg := loc.
 
Definition T :=
   fun (r : loc) =>
      match Loc.type r with Tint => R IT2 | Tfloat => R FT2 end.
 
Definition notemporary := fun (r : loc) => forall x,  Loc.diff r (T x).
 
Definition Move := (Reg * Reg)%type.
 
Definition Moves := list Move.
 
Definition State := ((Moves * Moves) * Moves)%type.
 
Definition StateToMove (r : State) : Moves :=
   match r with ((t, b), l) => t end.
 
Definition StateBeing (r : State) : Moves :=
   match r with ((t, b), l) => b end.
 
Definition StateDone (r : State) : Moves :=
   match r with ((t, b), l) => l end.
 
Fixpoint noRead (p : Moves) (r : Reg) {struct p} : Prop :=
 match p with
   nil => True
  | (s, d) :: l => Loc.diff s r /\ noRead l r
 end.
 
Lemma noRead_app:
 forall (l1 l2 : Moves) (r : Reg),
 noRead l1 r -> noRead l2 r ->  noRead (l1 ++ l2) r.
Proof.
intros; induction l1 as [|a l1 Hrecl1]; simpl; auto.
destruct a.
elim H; intros; split; auto.
Qed.
 
Inductive step : State -> State ->  Prop :=
  step_nop:
    forall (r : Reg) (t1 t2 l : Moves),
     step (t1 ++ ((r, r) :: t2), nil, l) (t1 ++ t2, nil, l)
 | step_start:
     forall (t1 t2 l : Moves) (m : Move),
      step (t1 ++ (m :: t2), nil, l) (t1 ++ t2, m :: nil, l)
 | step_push:
     forall (t1 t2 b l : Moves) (s d r : Reg),
      step
       (t1 ++ ((d, r) :: t2), (s, d) :: b, l)
       (t1 ++ t2, (d, r) :: ((s, d) :: b), l)
 | step_loop:
     forall (t b l : Moves) (s d r0 r0ounon : Reg),
      step
       (t, (s, r0ounon) :: (b ++ ((r0, d) :: nil)), l)
       (t, (s, r0ounon) :: (b ++ ((T r0, d) :: nil)), (r0, T r0) :: l)
 | step_pop:
     forall (t b l : Moves) (s0 d0 sn dn : Reg),
     noRead t dn ->
     Loc.diff dn s0 ->
      step
       (t, (sn, dn) :: (b ++ ((s0, d0) :: nil)), l)
       (t, b ++ ((s0, d0) :: nil), (sn, dn) :: l)
 | step_last:
     forall (t l : Moves) (s d : Reg),
     noRead t d ->  step (t, (s, d) :: nil, l) (t, nil, (s, d) :: l) .
Hint Resolve step_nop step_start step_push step_loop step_pop step_last .
 
Fixpoint path (l : Moves) : Prop :=
 match l with
   nil => True
  | (s, d) :: l =>
      match l with
        nil => True
       | (ss, dd) :: l2 => s = dd /\ path l
      end
 end.
 
Lemma path_pop: forall (m : Move) (l : Moves), path (m :: l) ->  path l.
Proof.
simpl; intros m l; destruct m as [ms md]; case l; auto.
intros m0; destruct m0; intros; inversion H; auto.
Qed.
 
Fixpoint noWrite (p : Moves) (r : Reg) {struct p} : Prop :=
 match p with
   nil => True
  | (s, d) :: l => Loc.diff d r /\ noWrite l r
 end.
 
Lemma noWrite_pop:
 forall (p1 p2 : Moves) (m : Move) (r : Reg),
 noWrite (p1 ++ (m :: p2)) r ->  noWrite (p1 ++ p2) r.
Proof.
intros; induction p1 as [|a p1 Hrecp1].
generalize H; simpl; case m; intros; inversion H0; auto.
generalize H; rewrite app_cons; rewrite app_cons.
simpl; case a; intros.
inversion H0; split; auto.
Qed.
 
Lemma noWrite_in:
 forall (p1 p2 : Moves) (r0 r1 r2 : Reg),
 noWrite (p1 ++ ((r1, r2) :: p2)) r0 ->  Loc.diff r0 r2.
Proof.
intros; induction p1 as [|a p1 Hrecp1]; simpl; auto.
generalize H; simpl; intros; inversion H0; auto.
apply Loc.diff_sym; auto.
generalize H; rewrite app_cons; simpl; case a; intros.
apply Hrecp1; inversion H0; auto.
Qed.
 
Lemma noWrite_swap:
 forall (p : Moves) (m1 m2 : Move) (r : Reg),
 noWrite (m1 :: (m2 :: p)) r ->  noWrite (m2 :: (m1 :: p)) r.
Proof.
intros p m1 m2 r; simpl; case m1; case m2.
intros; inversion H; inversion H1; split; auto.
Qed.
 
Lemma noWrite_movFront:
 forall (p1 p2 : Moves) (m : Move) (r0 : Reg),
 noWrite (p1 ++ (m :: p2)) r0 ->  noWrite (m :: (p1 ++ p2)) r0.
Proof.
intros p1 p2 m r0; induction p1 as [|a p1 Hrecp1]; auto.
case a; intros r1 r2; rewrite app_cons; rewrite app_cons.
intros; apply noWrite_swap; rewrite <- app_cons.
simpl in H |-; inversion H; unfold noWrite; fold noWrite; auto.
Qed.
 
Lemma noWrite_insert:
 forall (p1 p2 : Moves) (m : Move) (r0 : Reg),
 noWrite (m :: (p1 ++ p2)) r0 ->  noWrite (p1 ++ (m :: p2)) r0.
Proof.
intros p1 p2 m r0; induction p1 as [|a p1 Hrecp1].
simpl; auto.
destruct a; simpl.
destruct m.
intros [H1 [H2 H3]]; split; auto.
apply Hrecp1.
simpl; auto.
Qed.
 
Lemma noWrite_tmpLast:
 forall (t : Moves) (r s d : Reg),
 noWrite (t ++ ((s, d) :: nil)) r ->
 forall (x : Reg),  noWrite (t ++ ((x, d) :: nil)) r.
Proof.
intros; induction t as [|a t Hrect].
simpl; auto.
generalize H; simpl; case a; intros; inversion H0; split; auto.
Qed.
 
Fixpoint simpleDest (p : Moves) : Prop :=
 match p with
   nil => True
  | (s, d) :: l => noWrite l d /\ simpleDest l
 end.
 
Lemma simpleDest_Pop:
 forall (m : Move) (l1 l2 : Moves),
 simpleDest (l1 ++ (m :: l2)) ->  simpleDest (l1 ++ l2).
Proof.
intros; induction l1 as [|a l1 Hrecl1].
generalize H; simpl; case m; intros; inversion H0; auto.
generalize H; rewrite app_cons; rewrite app_cons.
simpl; case a; intros; inversion H0; split; auto.
apply (noWrite_pop l1 l2 m); auto.
Qed.
 
Lemma simpleDest_pop:
 forall (m : Move) (l : Moves), simpleDest (m :: l) ->  simpleDest l.
Proof.
intros m l; simpl; case m; intros _ r [X Y]; auto.
Qed.
 
Lemma simpleDest_right:
 forall (l1 l2 : Moves), simpleDest (l1 ++ l2) ->  simpleDest l2.
Proof.
intros l1; induction l1 as [|a l1 Hrecl1]; auto.
intros l2; rewrite app_cons; intros; apply Hrecl1.
apply (simpleDest_pop a); auto.
Qed.
 
Lemma simpleDest_swap:
 forall (m1 m2 : Move) (l : Moves),
 simpleDest (m1 :: (m2 :: l)) ->  simpleDest (m2 :: (m1 :: l)).
Proof.
intros m1 m2 l; simpl; case m1; case m2.
intros _ r0 _ r2 [[X Y] [Z U]]; auto.
(repeat split); auto.
apply Loc.diff_sym; auto.
Qed.
 
Lemma simpleDest_pop2:
 forall (m1 m2 : Move) (l : Moves),
 simpleDest (m1 :: (m2 :: l)) ->  simpleDest (m1 :: l).
Proof.
intros; apply (simpleDest_pop m2); apply simpleDest_swap; auto.
Qed.
 
Lemma simpleDest_movFront:
 forall (p1 p2 : Moves) (m : Move),
 simpleDest (p1 ++ (m :: p2)) ->  simpleDest (m :: (p1 ++ p2)).
Proof.
intros p1 p2 m; induction p1 as [|a p1 Hrecp1].
simpl; auto.
rewrite app_cons; rewrite app_cons.
case a; intros; simpl in H |-; inversion H.
apply simpleDest_swap; simpl; auto.
destruct m.
cut (noWrite ((r1, r2) :: (p1 ++ p2)) r0).
cut (simpleDest ((r1, r2) :: (p1 ++ p2))).
intro; (repeat split); elim H3; elim H2; intros; auto.
apply Hrecp1; auto.
apply noWrite_movFront; auto.
Qed.
 
Lemma simpleDest_insert:
 forall (p1 p2 : Moves) (m : Move),
 simpleDest (m :: (p1 ++ p2)) ->  simpleDest (p1 ++ (m :: p2)).
Proof.
intros p1 p2 m; induction p1 as [|a p1 Hrecp1].
simpl; auto.
rewrite app_cons; intros.
simpl.
destruct a as [a1 a2].
split.
destruct m; simpl in H |-.
apply noWrite_insert.
simpl; split; elim H; intros [H1 H2] [H3 H4]; auto.
apply Loc.diff_sym; auto.
apply Hrecp1.
apply simpleDest_pop2 with (a1, a2); auto.
Qed.
 
Lemma simpleDest_movBack:
 forall (p1 p2 : Moves) (m : Move),
 simpleDest (p1 ++ (m :: p2)) ->  simpleDest ((p1 ++ p2) ++ (m :: nil)).
Proof.
intros.
apply (simpleDest_insert (p1 ++ p2) nil m).
rewrite app_nil; apply simpleDest_movFront; auto.
Qed.
 
Lemma simpleDest_swap_app:
 forall (t1 t2 t3 : Moves) (m : Move),
 simpleDest (t1 ++ (m :: (t2 ++ t3))) ->  simpleDest ((t1 ++ t2) ++ (m :: t3)).
Proof.
intros.
apply (simpleDest_insert (t1 ++ t2) t3 m).
rewrite <- app_app.
apply simpleDest_movFront; auto.
Qed.
 
Lemma simpleDest_tmpLast:
 forall (t : Moves) (s d : Reg),
 simpleDest (t ++ ((s, d) :: nil)) ->
 forall (r : Reg),  simpleDest (t ++ ((r, d) :: nil)).
Proof.
intros t s d; induction t as [|a t Hrect].
simpl; auto.
simpl; case a; intros; inversion H; split; auto.
apply (noWrite_tmpLast t r0 s); auto.
Qed.
 
Fixpoint noTmp (b : Moves) : Prop :=
 match b with
   nil => True
  | (s, d) :: l =>
      (forall r,  Loc.diff s (T r)) /\
      ((forall r,  Loc.diff d (T r)) /\ noTmp l)
 end.
 
Fixpoint noTmpLast (b : Moves) : Prop :=
 match b with
   nil => True
  | (s, d) :: nil => forall r,  Loc.diff d (T r)
  | (s, d) :: l =>
      (forall r,  Loc.diff s (T r)) /\
      ((forall r,  Loc.diff d (T r)) /\ noTmpLast l)
 end.
 
Lemma noTmp_app:
 forall (l1 l2 : Moves) (m : Move),
 noTmp l1 -> noTmpLast (m :: l2) ->  noTmpLast (l1 ++ (m :: l2)).
Proof.
intros.
induction l1 as [|a l1 Hrecl1].
simpl; auto.
simpl.
caseEq (l1 ++ (m :: l2)); intro.
destruct a.
elim H; intros; auto.
inversion H; auto.
elim H3; auto.
intros; destruct a as [a1 a2].
elim H; intros H2 [H3 H4]; auto.
(repeat split); auto.
rewrite H1 in Hrecl1; apply Hrecl1; auto.
Qed.
 
Lemma noTmpLast_popBack:
 forall (t : Moves) (m : Move), noTmpLast (t ++ (m :: nil)) ->  noTmp t.
Proof.
intros.
induction t as [|a t Hrect].
simpl; auto.
destruct a as [a1 a2].
rewrite app_cons in H.
simpl.
simpl in H |-.
generalize H; caseEq (t ++ (m :: nil)); intros.
destruct t; inversion H0.
elim H1.
intros H2 [H3 H4]; (repeat split); auto.
rewrite <- H0 in H4.
apply Hrect; auto.
Qed.
 
Fixpoint getsrc (p : Moves) : list Reg :=
 match p with
   nil => nil
  | (s, d) :: l => s :: getsrc l
 end.
 
Fixpoint getdst (p : Moves) : list Reg :=
 match p with
   nil => nil
  | (s, d) :: l => d :: getdst l
 end.
 
Fixpoint noOverlap_aux (r : Reg) (l : list Reg) {struct l} : Prop :=
 match l with
   nil => True
  | b :: m => (b = r \/ Loc.diff b r) /\ noOverlap_aux r m
 end.
 
Definition noOverlap (p : Moves) : Prop :=
   forall l, In l (getsrc p) ->  noOverlap_aux l (getdst p).
 
Definition stepInv (r : State) : Prop :=
   path (StateBeing r) /\
   (simpleDest (StateToMove r ++ StateBeing r) /\
    (noOverlap (StateToMove r ++ StateBeing r) /\
     (noTmp (StateToMove r) /\ noTmpLast (StateBeing r)))).
 
Definition Value := val.
 
Definition Env := locset.
 
Definition get (e : Env) (r : Reg) := Locmap.get r e.
 
Definition update (e : Env) (r : Reg) (v : Value) : Env := Locmap.set r v e.
 
Fixpoint sexec (p : Moves) (e : Env) {struct p} : Env :=
 match p with
   nil => e
  | (s, d) :: l => let e' := sexec l e in
                     update e' d (get e' s)
 end.
 
Fixpoint pexec (p : Moves) (e : Env) {struct p} : Env :=
 match p with
   nil => e
  | (s, d) :: l => update (pexec l e) d (get e s)
 end.
 
Lemma get_update:
 forall (e : Env) (r1 r2 : Reg) (v : Value),
  get (update e r1 v) r2 =
  (if Loc.eq r1 r2 then v else if Loc.overlap r1 r2 then Vundef else get e r2).
Proof.
intros.
unfold update, get, Locmap.get, Locmap.set; trivial.
Qed.
 
Lemma get_update_id:
 forall (e : Env) (r1 : Reg) (v : Value),  get (update e r1 v) r1 = v.
Proof.
intros e r1 v; rewrite (get_update e r1 r1); auto.
case (Loc.eq r1 r1); auto.
intros H; elim H; trivial.
Qed.
 
Lemma get_update_diff:
 forall (e : Env) (r1 r2 : Reg) (v : Value),
 Loc.diff r1 r2 ->  get (update e r1 v) r2 = get e r2.
Proof.
intros; unfold update, get, Locmap.get, Locmap.set.
case (Loc.eq r1 r2); intro.
absurd (r1 = r2); [apply Loc.diff_not_eq; trivial | trivial].
caseEq (Loc.overlap r1 r2); intro; trivial.
absurd (Loc.diff r1 r2); [apply Loc.overlap_not_diff; assumption | assumption].
Qed.
 
Lemma get_update_ndiff:
 forall (e : Env) (r1 r2 : Reg) (v : Value),
 r1 <> r2 -> not (Loc.diff r1 r2) ->  get (update e r1 v) r2 = Vundef.
Proof.
intros; unfold update, get, Locmap.get, Locmap.set.
case (Loc.eq r1 r2); intro.
absurd (r1 = r2); assumption.
caseEq (Loc.overlap r1 r2); intro; trivial.
absurd (Loc.diff r1 r2); (try assumption).
apply Loc.non_overlap_diff; assumption.
Qed.
 
Lemma pexec_swap:
 forall (m1 m2 : Move) (t : Moves),
 simpleDest (m1 :: (m2 :: t)) ->
 forall (e : Env) (r : Reg),
  get (pexec (m1 :: (m2 :: t)) e) r = get (pexec (m2 :: (m1 :: t)) e) r.
Proof.
intros; destruct m1 as [m1s m1d]; destruct m2 as [m2s m2d].
generalize H; simpl; intros [[NEQ NW] [NW2 HSD]]; clear H.
case (Loc.eq m1d r); case (Loc.eq m2d r); intros.
absurd (m1d = m2d);
 [apply Loc.diff_not_eq; apply Loc.diff_sym; assumption |
  rewrite e0; rewrite e1; trivial].
caseEq (Loc.overlap m2d r); intro.
absurd (Loc.diff m2d m1d); [apply Loc.overlap_not_diff; rewrite e0 | idtac];
 (try assumption).
subst m1d; rewrite get_update_id; rewrite get_update_diff;
 (try rewrite get_update_id); auto.
caseEq (Loc.overlap m1d r); intro.
absurd (Loc.diff m1d m2d);
 [apply Loc.overlap_not_diff; rewrite e0 | apply Loc.diff_sym]; assumption.
subst m2d; (repeat rewrite get_update_id); rewrite get_update_diff;
 [rewrite get_update_id; trivial | apply Loc.diff_sym; trivial].
caseEq (Loc.overlap m1d r); caseEq (Loc.overlap m2d r); intros.
(repeat rewrite get_update_ndiff);
 (try (apply Loc.overlap_not_diff; assumption)); trivial.
assert (~ Loc.diff m1d r);
 [apply Loc.overlap_not_diff; assumption |
  intros; rewrite get_update_ndiff; auto].
rewrite get_update_diff;
 [rewrite get_update_ndiff; auto | apply Loc.non_overlap_diff; auto].
cut (~ Loc.diff m2d r); [idtac | apply Loc.overlap_not_diff; auto].
cut (Loc.diff m1d r); [idtac | apply Loc.non_overlap_diff; auto].
intros; rewrite get_update_diff; auto.
(repeat rewrite get_update_ndiff); auto.
cut (Loc.diff m1d r); [idtac | apply Loc.non_overlap_diff; auto].
cut (Loc.diff m2d r); [idtac | apply Loc.non_overlap_diff; auto].
intros; (repeat rewrite get_update_diff); auto.
Qed.
 
Lemma pexec_add:
 forall (t1 t2 : Moves) (r : Reg) (e : Env),
 get (pexec t1 e) r = get (pexec t2 e) r ->
 forall (a : Move),  get (pexec (a :: t1) e) r = get (pexec (a :: t2) e) r.
Proof.
intros.
case a.
simpl.
intros a1 a2.
unfold get, update, Locmap.set, Locmap.get.
case (Loc.eq a2 r); case (Loc.overlap a2 r); auto.
Qed.
 
Lemma pexec_movBack:
 forall (t1 t2 : Moves) (m : Move),
 simpleDest (m :: (t1 ++ t2)) ->
 forall (e : Env) (r : Reg),
  get (pexec (m :: (t1 ++ t2)) e) r = get (pexec (t1 ++ (m :: t2)) e) r.
Proof.
intros t1 t2 m; induction t1 as [|a t1 Hrect1].
simpl; auto.
rewrite app_cons.
intros; rewrite pexec_swap; auto; rewrite app_cons; auto.
apply pexec_add.
apply Hrect1.
apply (simpleDest_pop2 m a); auto.
Qed.
 
Lemma pexec_movFront:
 forall (t1 t2 : Moves) (m : Move),
 simpleDest (t1 ++ (m :: t2)) ->
 forall (e : Env) (r : Reg),
  get (pexec (t1 ++ (m :: t2)) e) r = get (pexec (m :: (t1 ++ t2)) e) r.
Proof.
intros; rewrite <- pexec_movBack; eauto.
apply simpleDest_movFront; auto.
Qed.
 
Lemma pexec_mov:
 forall (t1 t2 t3 : Moves) (m : Move),
 simpleDest ((t1 ++ (m :: t2)) ++ t3) ->
 forall (e : Env) (r : Reg),
  get (pexec ((t1 ++ (m :: t2)) ++ t3) e) r =
  get (pexec ((t1 ++ t2) ++ (m :: t3)) e) r.
Proof.
intros t1 t2 t3 m.
rewrite <- app_app.
rewrite app_cons.
intros.
rewrite pexec_movFront; auto.
cut (simpleDest (m :: (t1 ++ (t2 ++ t3)))).
rewrite app_app.
rewrite <- pexec_movFront; auto.
apply simpleDest_swap_app; auto.
apply simpleDest_movFront; auto.
Qed.
 
Definition diff_dec:
 forall (x y : Reg),  ({ Loc.diff x y }) + ({ not (Loc.diff x y) }).
intros.
case (Loc.eq x y).
intros heq; right.
red; intro; absurd (x = y); auto.
apply Loc.diff_not_eq; auto.
intro; caseEq (Loc.overlap x y).
intro; right.
apply Loc.overlap_not_diff; auto.
intro; left; apply Loc.non_overlap_diff; auto.
Defined.
 
Lemma get_pexec_id_noWrite:
 forall (t : Moves) (d : Reg),
 noWrite t d ->
 forall (e : Env) (v : Value),  v = get (pexec t (update e d v)) d.
Proof.
intros.
induction t as [|a t Hrect].
simpl.
rewrite get_update_id; auto.
generalize H; destruct a as [a1 a2]; simpl; intros [NEQ R].
rewrite get_update_diff; auto.
Qed.
 
Lemma pexec_nop:
 forall (t : Moves) (r : Reg) (e : Env) (x : Reg),
 Loc.diff r x ->  get (pexec ((r, r) :: t) e) x = get (pexec t e) x.
Proof.
intros.
simpl.
rewrite get_update_diff; auto.
Qed.
 
Lemma sD_nW: forall t r s, simpleDest ((s, r) :: t) ->  noWrite t r.
Proof.
induction t.
simpl; auto.
simpl.
destruct a.
intros r1 r2 H; split; [try assumption | idtac].
elim H;
 [intros H0 H1; elim H0; [intros H2 H3; (try clear H0 H); (try exact H2)]].
elim H;
 [intros H0 H1; elim H0; [intros H2 H3; (try clear H0 H); (try exact H3)]].
Qed.
 
Lemma sD_pexec:
 forall (t : Moves) (s d : Reg),
 simpleDest ((s, d) :: t) -> forall (e : Env),  get (pexec t e) d = get e d.
Proof.
intros.
induction t as [|a t Hrect]; simpl; auto.
destruct a as [a1 a2].
simpl in H |-; elim H; intros [H0 H1] [H2 H3]; clear H.
case (Loc.eq a2 d); intro.
absurd (a2 = d); [apply Loc.diff_not_eq | trivial]; assumption.
rewrite get_update_diff; (try assumption).
apply Hrect.
simpl; (split; assumption).
Qed.
 
Lemma noOverlap_nil: noOverlap nil.
Proof.
unfold noOverlap, noOverlap_aux, getsrc, getdst; trivial.
Qed.
 
Lemma getsrc_add:
 forall (m : Move) (l1 l2 : Moves) (l : Reg),
 In l (getsrc (l1 ++ l2)) ->  In l (getsrc (l1 ++ (m :: l2))).
Proof.
intros m l1 l2 l; destruct m; induction l1; simpl; auto.
destruct a; simpl; intros.
elim H; intros H0; [left | right]; auto.
Qed.
 
Lemma getdst_add:
 forall (r1 r2 : Reg) (l1 l2 : Moves),
  getdst (l1 ++ ((r1, r2) :: l2)) = getdst l1 ++ (r2 :: getdst l2).
Proof.
intros r1 r2 l1 l2; induction l1; simpl; auto.
destruct a; simpl; rewrite IHl1; auto.
Qed.
 
Lemma getdst_app:
 forall (l1 l2 : Moves),  getdst (l1 ++ l2) = getdst l1 ++ getdst l2.
Proof.
intros; induction l1; simpl; auto.
destruct a; simpl; rewrite IHl1; auto.
Qed.
 
Lemma noOverlap_auxpop:
 forall (x r : Reg) (l : list Reg),
 noOverlap_aux x (r :: l) ->  noOverlap_aux x l.
Proof.
induction l; simpl; auto.
intros [H1 [H2 H3]]; split; auto.
Qed.
 
Lemma noOverlap_auxPop:
 forall (x r : Reg) (l1 l2 : list Reg),
 noOverlap_aux x (l1 ++ (r :: l2)) ->  noOverlap_aux x (l1 ++ l2).
Proof.
intros x r l1 l2; (try assumption).
induction l1 as [|a l1 Hrecl1]; simpl app.
intro; apply (noOverlap_auxpop x r); auto.
(repeat rewrite app_cons); simpl.
intros [H1 H2]; split; auto.
Qed.
 
Lemma noOverlap_pop:
 forall (m : Move) (l : Moves), noOverlap (m :: l) ->  noOverlap l.
Proof.
induction l.
intro; apply noOverlap_nil.
unfold noOverlap; simpl; destruct m; destruct a; simpl; intros.
elim (H l0); intros; (try assumption).
elim H0; intros H1; right; [left | right]; assumption.
Qed.
 
Lemma noOverlap_Pop:
 forall (m : Move) (l1 l2 : Moves),
 noOverlap (l1 ++ (m :: l2)) ->  noOverlap (l1 ++ l2).
Proof.
intros m l1 l2; induction l1 as [|a l1 Hrecl1]; simpl.
simpl; apply noOverlap_pop.
(repeat rewrite app_cons); unfold noOverlap; destruct a; simpl.
intros H l H0; split.
elim (H l); [intros H1 H2 | idtac]; auto.
elim H0; [intros H3; left | intros H3; right; apply getsrc_add]; auto.
unfold noOverlap in Hrecl1 |-.
elim H0; intros H1; clear H0.
destruct m; rewrite getdst_app; apply noOverlap_auxPop with ( r := r2 ).
rewrite getdst_add in H.
elim H with ( l := l ); [intros H0 H2; (try clear H); (try exact H2) | idtac].
left; (try assumption).
apply Hrecl1 with ( l := l ); auto.
intros l0 H0; (try assumption).
elim H with ( l := l0 ); [intros H2 H3; (try clear H); (try exact H3) | idtac];
 auto.
Qed.
 
Lemma noOverlap_right:
 forall (l1 l2 : Moves), noOverlap (l1 ++ l2) ->  noOverlap l2.
Proof.
intros l1; induction l1 as [|a l1 Hrecl1]; auto.
intros l2; rewrite app_cons; intros; apply Hrecl1.
apply (noOverlap_pop a); auto.
Qed.
 
Lemma pexec_update:
 forall t e d r v,
 Loc.diff d r ->
 noRead t d ->  get (pexec t (update e d v)) r = get (pexec t e) r.
Proof.
induction t; simpl.
intros; rewrite get_update_diff; auto.
destruct a as [a1 a2]; intros; case (Loc.eq a2 r); intro.
subst a2; (repeat rewrite get_update_id).
rewrite get_update_diff; auto; apply Loc.diff_sym; elim H0; auto.
case (diff_dec a2 r); intro.
(repeat rewrite get_update_diff); auto.
apply IHt; auto.
elim H0; auto.
(repeat rewrite get_update_ndiff); auto.
Qed.
 
Lemma pexec_push:
 forall (t l : Moves) (s d : Reg),
 noRead t d ->
 simpleDest ((s, d) :: t) ->
 forall (e : Env) (r : Reg),
 r = d \/ Loc.diff d r ->
  get (pexec ((s, d) :: t) (sexec l e)) r =
  get (pexec t (sexec ((s, d) :: l) e)) r.
Proof.
intros; simpl.
elim H1; intros e1.
rewrite e1; rewrite get_update_id; auto.
rewrite (sD_pexec t s d); auto; rewrite get_update_id; auto.
rewrite pexec_update; auto.
rewrite get_update_diff; auto.
Qed.
 
Definition exec (s : State) (e : Env) :=
   pexec (StateToMove s ++ StateBeing s) (sexec (StateDone s) e).
 
Definition sameEnv (e1 e2 : Env) :=
   forall (r : Reg), notemporary r ->  get e1 r = get e2 r.
 
Definition NoOverlap (r : Reg) (s : State) :=
   noOverlap ((r, r) :: (StateToMove s ++ StateBeing s)).
 
Lemma noOverlapaux_swap2:
 forall (l1 l2 : list Reg) (m l : Reg),
 noOverlap_aux l (l1 ++ (m :: l2)) ->  noOverlap_aux l (m :: (l1 ++ l2)).
Proof.
intros l1 l2 m l; induction l1; simpl noOverlap_aux; auto.
intros; elim H; intros H0 H1; (repeat split); auto.
simpl in IHl1 |-.
elim IHl1; [intros H2 H3; (try exact H2) | idtac]; auto.
apply (noOverlap_auxpop l m).
apply IHl1; auto.
Qed.
 
Lemma noTmp_noReadTmp: forall t, noTmp t -> forall s,  noRead t (T s).
Proof.
induction t; simpl; auto.
destruct a as [a1 a2]; intros.
split; [idtac | apply IHt]; elim H; intros H1 [H2 H3]; auto.
Qed.
 
Lemma noRead_by_path:
 forall (b t : Moves) (r0 r1 r7 r8 : Reg),
 simpleDest ((r7, r8) :: (b ++ ((r0, r1) :: nil))) ->
 path (b ++ ((r0, r1) :: nil)) -> Loc.diff r8 r0 ->  noRead b r8.
Proof.
intros; induction b as [|a b Hrecb]; simpl; auto.
destruct a as [a1 a2]; generalize H H0; rewrite app_cons; intros; split.
simpl in H3 |-; caseEq (b ++ ((r0, r1) :: nil)); intro.
destruct b; inversion H4.
intros l H4.
rewrite H4 in H3.
destruct m.
rewrite H4 in H2; simpl in H2 |-.
elim H3; [intros H5 H6; (try clear H3); (try exact H5)].
rewrite H5.
elim H2; intros [H3 [H7 H8]] [H9 [H10 H11]]; (try assumption).
apply Hrecb.
apply (simpleDest_pop (a1, a2)); apply simpleDest_swap; auto.
apply (path_pop (a1, a2)); auto.
Qed.
 
Lemma noOverlap_swap:
 forall (m1 m2 : Move) (l : Moves),
 noOverlap (m1 :: (m2 :: l)) ->  noOverlap (m2 :: (m1 :: l)).
Proof.
intros m1 m2 l; simpl; destruct m1 as [m1s m1d]; destruct m2 as [m2s m2d].
unfold noOverlap; simpl; intros.
assert (m1s = l0 \/ (m2s = l0 \/ In l0 (getsrc l))).
elim H0; [intros H1 | intros [H1|H2]].
right; left; (try assumption).
left; (try assumption).
right; right; (try assumption).
(repeat split);
 (elim (H l0); [intros H2 H3; elim H3; [intros H4 H5] | idtac]; auto).
Qed.
 
Lemma getsrc_add1:
 forall (r1 r2 : Reg) (l1 l2 : Moves),
  getsrc (l1 ++ ((r1, r2) :: l2)) = getsrc l1 ++ (r1 :: getsrc l2).
Proof.
intros r1 r2 l1 l2; induction l1; simpl; auto.
destruct a; simpl; rewrite IHl1; auto.
Qed.
 
Lemma getsrc_app:
 forall (l1 l2 : Moves),  getsrc (l1 ++ l2) = getsrc l1 ++ getsrc l2.
Proof.
intros; induction l1; simpl; auto.
destruct a; simpl; rewrite IHl1; auto.
Qed.
 
Lemma Ingetsrc_swap:
 forall (m : Move) (l1 l2 : Moves) (l : Reg),
 In l (getsrc (m :: (l1 ++ l2))) ->  In l (getsrc (l1 ++ (m :: l2))).
Proof.
intros; destruct m as [m1 m2]; simpl; auto.
simpl in H |-.
elim H; intros H0; auto.
rewrite H0; rewrite getsrc_add1; auto.
apply (in_or_app (getsrc l1) (l :: getsrc l2)); auto.
right; apply in_eq; auto.
apply getsrc_add; auto.
Qed.
 
Lemma noOverlap_movFront:
 forall (p1 p2 : Moves) (m : Move),
 noOverlap (p1 ++ (m :: p2)) ->  noOverlap (m :: (p1 ++ p2)).
Proof.
intros p1 p2 m; unfold noOverlap.
destruct m; rewrite getdst_add; simpl getdst; rewrite getdst_app; intros.
apply noOverlapaux_swap2.
apply (H l); apply Ingetsrc_swap; auto.
Qed.
 
Lemma step_inv_loop_aux:
 forall (t l : Moves) (s d : Reg),
 simpleDest (t ++ ((s, d) :: nil)) ->
 noTmp t ->
 forall (e : Env) (r : Reg),
 notemporary r ->
 d = r \/ Loc.diff d r ->
  get (pexec (t ++ ((s, d) :: nil)) (sexec l e)) r =
  get (pexec (t ++ ((T s, d) :: nil)) (sexec ((s, T s) :: l) e)) r.
Proof.
intros; (repeat rewrite pexec_movFront); auto.
(repeat rewrite app_nil); simpl; elim H2; intros e1.
subst d; (repeat rewrite get_update_id); auto.
(repeat rewrite get_update_diff); auto.
rewrite pexec_update; auto.
apply Loc.diff_sym; unfold notemporary in H1 |-; auto.
apply noTmp_noReadTmp; auto.
apply (simpleDest_tmpLast t s); auto.
Qed.
 
Lemma step_inv_loop:
 forall (t l : Moves) (s d : Reg),
 simpleDest (t ++ ((s, d) :: nil)) ->
 noTmpLast (t ++ ((s, d) :: nil)) ->
 forall (e : Env) (r : Reg),
 notemporary r ->
 d = r \/ Loc.diff d r ->
  get (pexec (t ++ ((s, d) :: nil)) (sexec l e)) r =
  get (pexec (t ++ ((T s, d) :: nil)) (sexec ((s, T s) :: l) e)) r.
Proof.
intros; apply step_inv_loop_aux; auto.
apply (noTmpLast_popBack t (s, d)); auto.
Qed.
 
Definition sameExec (s1 s2 : State) :=
   forall (e : Env) (r : Reg),
    (let A :=
      getdst
       ((StateToMove s1 ++ StateBeing s1) ++ (StateToMove s2 ++ StateBeing s2))
      in
       notemporary r ->
       (forall x, In x A ->  r = x \/ Loc.diff r x) ->
        get (exec s1 e) r = get (exec s2 e) r).
 
Lemma get_noWrite:
 forall (t : Moves) (d : Reg),
 noWrite t d -> forall (e : Env),  get e d = get (pexec t e) d.
Proof.
intros; induction t as [|a t Hrect]; simpl; auto.
generalize H; destruct a as [a1 a2]; simpl; intros [NEQ R].
unfold get, Locmap.get, update, Locmap.set.
case (Loc.eq a2 d); intro; auto.
absurd (a2 = d); auto; apply Loc.diff_not_eq; (try assumption).
caseEq (Loc.overlap a2 d); intro.
absurd (Loc.diff a2 d); auto; apply Loc.overlap_not_diff; auto.
unfold get, Locmap.get in Hrect |-; apply Hrect; auto.
Qed.
 
Lemma step_sameExec:
 forall (r1 r2 : State), step r1 r2 -> stepInv r1 ->  sameExec r1 r2.
Proof.
intros r1 r2 STEP; inversion STEP;
 unfold stepInv, sameExec, NoOverlap, exec, StateToMove, StateBeing, StateDone;
 (repeat rewrite app_nil); intros [P [SD [NO [TT TB]]]]; intros.
rewrite pexec_movFront; simpl; auto.
case (Loc.eq r r0); intros e0.
subst r0; rewrite get_update_id; apply get_noWrite; apply sD_nW with r;
 apply simpleDest_movFront; auto.
elim H2 with ( x := r );
 [intros H3; absurd (r = r0); auto |
  intros H3; rewrite get_update_diff; auto; apply Loc.diff_sym; auto | idtac].
(repeat (rewrite getdst_app; simpl)); apply in_or_app; left; apply in_or_app;
 right; simpl; auto.
(repeat rewrite pexec_movFront); auto.
rewrite app_nil; auto.
apply simpleDest_movBack; auto.
apply pexec_mov; auto.
repeat (rewrite <- app_cons; rewrite app_app).
apply step_inv_loop; auto.
repeat (rewrite <- app_app; rewrite app_cons; auto).
repeat (rewrite <- app_app; rewrite app_cons; auto).
apply noTmp_app; auto.
elim H2 with ( x := d );
 [intros H3; left; auto | intros H3; right; apply Loc.diff_sym; auto
  | try clear H2].
repeat (rewrite getdst_app; simpl).
apply in_or_app; left; apply in_or_app; right; simpl; right; apply in_or_app;
 right; simpl; left; trivial.
rewrite pexec_movFront; auto; apply pexec_push; auto.
apply noRead_app; auto.
apply noRead_app.
apply (noRead_by_path b b s0 d0 sn dn); auto.
apply (simpleDest_right t); auto.
apply (path_pop (sn, dn)); auto.
simpl; split; [apply Loc.diff_sym | idtac]; auto.
apply simpleDest_movFront; auto.
elim H4 with ( x := dn ); [intros H5 | intros H5 | try clear H4].
left; (try assumption).
right; apply Loc.diff_sym; (try assumption).
repeat (rewrite getdst_app; simpl).
apply in_or_app; left; apply in_or_app; right; simpl; left; trivial.
rewrite pexec_movFront; auto.
rewrite app_nil; auto.
apply pexec_push; auto.
rewrite <- (app_nil _ t).
apply simpleDest_movFront; auto.
elim (H3 d); (try intros H4).
left; (try assumption).
right; apply Loc.diff_sym; (try assumption).
(repeat rewrite getdst_app); simpl; apply in_or_app; left; apply in_or_app;
 right; simpl; left; trivial.
Qed.
 
Lemma path_tmpLast:
 forall (s d : Reg) (l : Moves),
 path (l ++ ((s, d) :: nil)) ->  path (l ++ ((T s, d) :: nil)).
Proof.
intros; induction l as [|a l Hrecl].
simpl; auto.
generalize H; (repeat rewrite app_cons).
case a; generalize Hrecl; case l; intros; auto.
destruct m; intros.
inversion H0; split; auto.
Qed.
 
Lemma step_inv_path:
 forall (r1 r2 : State), step r1 r2 -> stepInv r1 ->  path (StateBeing r2).
Proof.
intros r1 r2 STEP; inversion_clear STEP; unfold stepInv;
 unfold stepInv, sameExec, sameEnv, exec, StateToMove, StateBeing, StateDone;
 intros [P [SD [TT TB]]]; (try (simpl; auto; fail)).
simpl; case m; auto.
generalize P; rewrite <- app_cons; rewrite <- app_cons.
apply (path_tmpLast r0).
generalize P; apply path_pop.
Qed.
 
Lemma step_inv_simpleDest:
 forall (r1 r2 : State),
 step r1 r2 -> stepInv r1 ->  simpleDest (StateToMove r2 ++ StateBeing r2).
Proof.
intros r1 r2 STEP; inversion_clear STEP; unfold stepInv;
 unfold stepInv, sameExec, sameEnv, exec, StateToMove, StateBeing, StateDone;
 (repeat rewrite app_nil); intros [P [SD [TT TB]]].
apply (simpleDest_Pop (r, r)); assumption.
apply simpleDest_movBack; assumption.
apply simpleDest_insert; rewrite <- app_app; apply simpleDest_movFront.
rewrite <- app_cons; rewrite app_app; auto.
generalize SD; (repeat rewrite <- app_cons); (repeat rewrite app_app).
generalize (simpleDest_tmpLast (t ++ ((s, r0ounon) :: b)) r0 d); auto.
generalize SD; apply simpleDest_Pop.
rewrite <- (app_nil _ t); generalize SD; apply simpleDest_Pop.
Qed.
 
Lemma noTmp_pop:
 forall (m : Move) (l1 l2 : Moves), noTmp (l1 ++ (m :: l2)) ->  noTmp (l1 ++ l2).
Proof.
intros; induction l1 as [|a l1 Hrecl1]; generalize H.
simpl; case m; intros; inversion H0; inversion H2; auto.
rewrite app_cons; rewrite app_cons; simpl; case a.
intros; inversion H0; inversion H2; auto.
Qed.
 
Lemma step_inv_noTmp:
 forall (r1 r2 : State), step r1 r2 -> stepInv r1 ->  noTmp (StateToMove r2).
Proof.
intros r1 r2 STEP; inversion_clear STEP; unfold stepInv;
 unfold stepInv, sameExec, sameEnv, exec, StateToMove, StateBeing, StateDone;
 intros [P [SD [NO [TT TB]]]]; generalize TT; (try apply noTmp_pop); auto.
Qed.
 
Lemma noTmp_noTmpLast: forall (l : Moves), noTmp l ->  noTmpLast l.
Proof.
intros; induction l as [|a l Hrecl]; (try (simpl; auto; fail)).
generalize H; simpl; case a; generalize Hrecl; case l;
 (intros; inversion H0; inversion H2; auto).
Qed.
 
Lemma noTmpLast_pop:
 forall (m : Move) (l : Moves), noTmpLast (m :: l) ->  noTmpLast l.
Proof.
intros m l; simpl; case m; case l.
simpl; auto.
intros; inversion H; inversion H1; auto.
Qed.
 
Lemma noTmpLast_Pop:
 forall (m : Move) (l1 l2 : Moves),
 noTmpLast (l1 ++ (m :: l2)) ->  noTmpLast (l1 ++ l2).
Proof.
intros; induction l1 as [|a l1 Hrecl1]; generalize H.
simpl; case m; case l2.
simpl; auto.
intros.
elim H0; [intros H1 H2; elim H2; [intros H3 H4; (try exact H4)]].
(repeat rewrite app_cons); simpl; case a.
generalize Hrecl1; case l1.
simpl; case m; case l2; intros; inversion H0; inversion H2; auto.
intros m0 l R r r0; rewrite app_cons; rewrite app_cons.
intros; inversion H0; inversion H2; auto.
Qed.
 
Lemma noTmpLast_push:
 forall (m : Move) (t1 t2 t3 : Moves),
 noTmp (t1 ++ (m :: t2)) -> noTmpLast t3 ->  noTmpLast (m :: t3).
Proof.
intros; induction t1 as [|a t1 Hrect1]; generalize H.
simpl; case m; intros r r0 [N1 [N2 NT]]; generalize H0; case t3; auto.
rewrite app_cons; intros; apply Hrect1.
generalize H1.
simpl; case m; case a; intros; inversion H2; inversion H4; auto.
Qed.
 
Lemma noTmpLast_tmpLast:
 forall (s d : Reg) (l : Moves),
 noTmpLast (l ++ ((s, d) :: nil)) ->  noTmpLast (l ++ ((T s, d) :: nil)).
Proof.
intros; induction l as [|a l Hrecl].
simpl; auto.
generalize H; rewrite app_cons; rewrite app_cons; simpl.
case a; generalize Hrecl; case l.
simpl; auto.
intros m l0 REC r r0; generalize REC; rewrite app_cons; rewrite app_cons.
case m; intros; inversion H0; inversion H2; split; auto.
Qed.
 
Lemma step_inv_noTmpLast:
 forall (r1 r2 : State), step r1 r2 -> stepInv r1 ->  noTmpLast (StateBeing r2).
Proof.
intros r1 r2 STEP; inversion_clear STEP; unfold stepInv;
 unfold stepInv, sameExec, sameEnv, exec, StateToMove, StateBeing, StateDone;
 intros [P [SD [NO [TT TB]]]]; auto.
apply (noTmpLast_push m t1 t2); auto.
apply (noTmpLast_push (d, r) t1 t2); auto.
generalize TB; rewrite <- app_cons; rewrite <- app_cons; apply noTmpLast_tmpLast.
apply (noTmpLast_pop (sn, dn)); auto.
Qed.
 
Lemma noOverlapaux_insert:
 forall (l1 l2 : list Reg) (r x : Reg),
 noOverlap_aux x (r :: (l1 ++ l2)) ->  noOverlap_aux x (l1 ++ (r :: l2)).
Proof.
simpl; intros; induction l1; simpl; split.
elim H; [intros H0 H1; (try exact H0)].
elim H; [intros H0 H1; (try exact H1)].
simpl in H |-.
elim H;
 [intros H0 H1; elim H1; [intros H2 H3; (try clear H1 H); (try exact H2)]].
apply IHl1.
split.
elim H; [intros H0 H1; (try exact H0)].
rewrite app_cons in H.
apply noOverlap_auxpop with ( r := a ).
elim H; [intros H0 H1; (try exact H1)].
Qed.
 
Lemma Ingetsrc_swap2:
 forall (m : Move) (l1 l2 : Moves) (l : Reg),
 In l (getsrc (l1 ++ (m :: l2))) ->  In l (getsrc (m :: (l1 ++ l2))).
Proof.
intros; destruct m as [m1 m2]; simpl; auto.
induction l1; simpl.
simpl in H |-; auto.
destruct a; simpl.
simpl in H |-.
elim H; [intros H0 | intros H0; (try exact H0)].
right; left; (try assumption).
elim IHl1; intros; auto.
Qed.
 
Lemma noOverlap_insert:
 forall (p1 p2 : Moves) (m : Move),
 noOverlap (m :: (p1 ++ p2)) ->  noOverlap (p1 ++ (m :: p2)).
Proof.
unfold noOverlap; destruct m; rewrite getdst_add; simpl getdst;
 rewrite getdst_app.
intros.
apply noOverlapaux_insert.
generalize (H l); intros H1; lapply H1;
 [intros H2; (try clear H1); (try exact H2) | idtac].
simpl getsrc.
generalize (Ingetsrc_swap2 (r, r0)); simpl; (intros; auto).
Qed.
 
Lemma noOverlap_movBack:
 forall (p1 p2 : Moves) (m : Move),
 noOverlap (p1 ++ (m :: p2)) ->  noOverlap ((p1 ++ p2) ++ (m :: nil)).
Proof.
intros.
apply (noOverlap_insert (p1 ++ p2) nil m).
rewrite app_nil; apply noOverlap_movFront; auto.
Qed.
 
Lemma noOverlap_movBack0:
 forall (t : Moves) (s d : Reg),
 noOverlap ((s, d) :: t) ->  noOverlap (t ++ ((s, d) :: nil)).
Proof.
intros t s d H; (try assumption).
apply noOverlap_insert.
rewrite app_nil; auto.
Qed.
 
Lemma noOverlap_Front0:
 forall (t : Moves) (s d : Reg),
 noOverlap (t ++ ((s, d) :: nil)) ->  noOverlap ((s, d) :: t).
Proof.
intros t s d H; (try assumption).
cut ((s, d) :: t = (s, d) :: (t ++ nil)).
intros e; rewrite e.
apply noOverlap_movFront; auto.
rewrite app_nil; auto.
Qed.
 
Lemma noTmpL_diff:
 forall (t : Moves) (s d : Reg),
 noTmpLast (t ++ ((s, d) :: nil)) ->  notemporary d.
Proof.
intros t s d; unfold notemporary; induction t; (try (simpl; intros; auto; fail)).
rewrite app_cons.
intros; apply IHt.
apply (noTmpLast_pop a); auto.
Qed.
 
Lemma noOverlap_aux_app:
 forall l1 l2 (r : Reg),
 noOverlap_aux r l1 -> noOverlap_aux r l2 ->  noOverlap_aux r (l1 ++ l2).
Proof.
induction l1; simpl; auto.
intros; split.
elim H; [intros H1 H2; (try clear H); (try exact H1)].
apply IHl1; auto.
elim H; [intros H1 H2; (try clear H); (try exact H2)].
Qed.
 
Lemma noTmP_noOverlap_aux:
 forall t (r : Reg), noTmp t ->  noOverlap_aux (T r) (getdst t).
Proof.
induction t; simpl; auto.
destruct a; simpl; (intros; split).
elim H; intros; elim H1; intros.
right; apply H2.
apply IHt; auto.
elim H;
 [intros H0 H1; elim H1; [intros H2 H3; (try clear H1 H); (try exact H3)]].
Qed.
 
Lemma noTmp_append: forall l1 l2, noTmp l1 -> noTmp l2 ->  noTmp (l1 ++ l2).
Proof.
induction l1; simpl; auto.
destruct a.
intros l2 [H1 [H2 H3]] H4.
(repeat split); auto.
Qed.
 
Lemma step_inv_noOverlap:
 forall (r1 r2 : State),
 step r1 r2 -> stepInv r1 ->  noOverlap (StateToMove r2 ++ StateBeing r2).
Proof.
intros r1 r2 STEP; inversion_clear STEP; unfold stepInv;
 unfold stepInv, sameExec, sameEnv, exec, StateToMove, StateBeing, StateDone;
 (repeat rewrite app_nil); intros [P [SD [NO [TT TB]]]];
 (try (generalize NO; apply noOverlap_Pop; auto; fail)).
apply noOverlap_movBack; auto.
apply noOverlap_insert; rewrite <- app_app; apply noOverlap_movFront;
 rewrite <- app_cons; rewrite app_app; auto.
generalize NO; (repeat rewrite <- app_cons); (repeat rewrite app_app);
 (clear NO; intros NO); apply noOverlap_movBack0.
assert (noOverlap ((r0, d) :: (t ++ ((s, r0ounon) :: b))));
 [apply noOverlap_Front0; auto | idtac].
generalize H; unfold noOverlap; simpl; clear H; intros.
elim H0; intros; [idtac | apply (H l0); (right; (try assumption))].
split; [right; (try assumption) | idtac].
generalize TB; simpl; caseEq (b ++ ((r0, d) :: nil)); intro.
elim (app_eq_nil b ((r0, d) :: nil)); intros; auto; inversion H4.
subst l0; intros; rewrite <- H1 in TB0.
elim TB0; [intros H2 H3; elim H3; [intros H4 H5; (try clear H3 TB0)]].
generalize (noTmpL_diff b r0 d); unfold notemporary; intro; apply H3; auto.
rewrite <- H1; apply noTmP_noOverlap_aux; apply noTmp_append; auto;
 rewrite <- app_cons in TB; apply noTmpLast_popBack with (r0, d); auto.
rewrite <- (app_nil _ t); apply (noOverlap_Pop (s, d)); assumption.
Qed.
 
Lemma step_inv: forall (r1 r2 : State), step r1 r2 -> stepInv r1 ->  stepInv r2.
Proof.
intros; unfold stepInv; (repeat split).
apply (step_inv_path r1 r2); auto.
apply (step_inv_simpleDest r1 r2); auto.
apply (step_inv_noOverlap r1 r2); auto.
apply (step_inv_noTmp r1 r2); auto.
apply (step_inv_noTmpLast r1 r2); auto.
Qed.
 
Definition step_NF (r : State) : Prop := ~ (exists s : State , step r s ).
 
Inductive stepp : State -> State ->  Prop :=
  stepp_refl: forall (r : State),  stepp r r
 | stepp_trans:
     forall (r1 r2 r3 : State), step r1 r2 -> stepp r2 r3 ->  stepp r1 r3 .
Hint Resolve stepp_refl stepp_trans .
 
Lemma stepp_transitive:
 forall (r1 r2 r3 : State), stepp r1 r2 -> stepp r2 r3 ->  stepp r1 r3.
Proof.
intros; induction H as [r|r1 r2 r0 H H1 HrecH]; eauto.
Qed.
 
Lemma step_stepp: forall (s1 s2 : State), step s1 s2 ->  stepp s1 s2.
Proof.
eauto.
Qed.
 
Lemma stepp_inv:
 forall (r1 r2 : State), stepp r1 r2 -> stepInv r1 ->  stepInv r2.
Proof.
intros; induction H as [r|r1 r2 r3 H H1 HrecH]; auto.
apply HrecH; auto.
apply (step_inv r1 r2); auto.
Qed.
 
Lemma noTmpLast_lastnoTmp:
 forall l s d, noTmpLast (l ++ ((s, d) :: nil)) ->  notemporary d.
Proof.
induction l.
simpl.
intros; unfold notemporary; auto.
destruct a as [a1 a2]; intros.
change (noTmpLast ((a1, a2) :: (l ++ ((s, d) :: nil)))) in H |-.
apply IHl with s.
apply noTmpLast_pop with (a1, a2); auto.
Qed.
 
Lemma step_inv_NoOverlap:
 forall (s1 s2 : State) r,
 step s1 s2 -> notemporary r -> stepInv s1 -> NoOverlap r s1 ->  NoOverlap r s2.
Proof.
intros s1 s2 r STEP notempr; inversion_clear STEP; unfold stepInv;
 unfold stepInv, sameExec, sameEnv, exec, StateToMove, StateBeing, StateDone;
 intros [P [SD [NO [TT TB]]]]; unfold NoOverlap; simpl.
simpl; (repeat rewrite app_nil); simpl; (repeat rewrite <- app_cons); intro;
 apply noOverlap_Pop with ( m := (r0, r0) ); auto.
(repeat rewrite app_nil); simpl; rewrite app_ass; (repeat rewrite <- app_cons);
 intro; rewrite ass_app; apply noOverlap_movBack; auto.
simpl; (repeat (rewrite app_ass; simpl)); (repeat rewrite <- app_cons); intro.
rewrite ass_app; apply noOverlap_insert; rewrite app_ass;
 apply noOverlap_movFront; auto.
simpl; (repeat rewrite <- app_cons); intro; rewrite ass_app;
 apply noOverlap_movBack0; auto.
generalize H; (repeat (rewrite app_ass; simpl)); intro.
assert (noOverlap ((r0, d) :: (((r, r) :: t) ++ ((s, r0ounon) :: b))));
 [apply noOverlap_Front0 | idtac]; auto.
generalize H0; (repeat (rewrite app_ass; simpl)); auto.
generalize H1; unfold noOverlap; simpl; intros.
elim H3; intros H4; clear H3.
split.
right; assert (notemporary d).
change (noTmpLast (((s, r0ounon) :: b) ++ ((r0, d) :: nil))) in TB |-;
 apply (noTmpLast_lastnoTmp ((s, r0ounon) :: b) r0); auto.
rewrite <- H4; unfold notemporary in H3 |-; apply H3.
split.
right; rewrite <- H4; unfold notemporary in notempr |-; apply notempr.
rewrite <- H4; apply noTmP_noOverlap_aux; auto.
apply noTmp_append; auto.
change (noTmpLast (((s, r0ounon) :: b) ++ ((r0, d) :: nil))) in TB |-;
 apply noTmpLast_popBack with ( m := (r0, d) ); auto.
apply (H2 l0).
elim H4; intros H3; right; [left | right]; assumption.
intro;
 change (noOverlap (((r, r) :: t) ++ ((sn, dn) :: (b ++ ((s0, d0) :: nil))))) in
 H1 |-.
change (noOverlap (((r, r) :: t) ++ (b ++ ((s0, d0) :: nil))));
 apply (noOverlap_Pop (sn, dn)); auto.
(repeat rewrite <- app_cons); apply noOverlap_Pop.
Qed.
 
Lemma step_inv_getdst:
 forall (s1 s2 : State) r,
 step s1 s2 ->
 In r (getdst (StateToMove s2 ++ StateBeing s2)) ->
  In r (getdst (StateToMove s1 ++ StateBeing s1)).
Proof.
intros s1 s2 r STEP; inversion_clear STEP;
 unfold StateToMove, StateBeing, StateDone.
(repeat rewrite getdst_app); simpl; (repeat rewrite app_nil); intro;
 apply in_or_app.
elim (in_app_or (getdst t1) (getdst t2) r); auto.
intro; right; simpl; right; assumption.
(repeat rewrite getdst_app); destruct m as [m1 m2]; simpl;
 (repeat rewrite app_nil); intro; apply in_or_app.
elim (in_app_or (getdst t1 ++ getdst t2) (m2 :: nil) r); auto; intro.
elim (in_app_or (getdst t1) (getdst t2) r); auto; intro.
right; simpl; right; assumption.
elim H0; intros H1; [right; simpl; left; (try assumption) | inversion H1].
(repeat rewrite getdst_app); simpl; (repeat rewrite app_nil); intro;
 apply in_or_app.
elim (in_app_or (getdst t1 ++ getdst t2) (r0 :: (d :: getdst b)) r); auto;
 intro.
elim (in_app_or (getdst t1) (getdst t2) r); auto; intro.
left; apply in_or_app; left; assumption.
left; apply in_or_app; right; simpl; right; assumption.
elim H0; intro.
left; apply in_or_app; right; simpl; left; trivial.
elim H1; intro.
right; (simpl; left; trivial).
right; simpl; right; assumption.
(repeat (rewrite getdst_app; simpl)); trivial.
(repeat (rewrite getdst_app; simpl)); intro.
elim (in_app_or (getdst t) (getdst b ++ (d0 :: nil)) r); auto; intro;
 apply in_or_app; auto.
elim (in_app_or (getdst b) (d0 :: nil) r); auto; intro.
right; simpl; right; apply in_or_app; auto.
elim H3; intro.
right; simpl; right; apply in_or_app; right; simpl; auto.
inversion H4.
rewrite app_nil; (repeat (rewrite getdst_app; simpl)); intro.
apply in_or_app; left; assumption.
Qed.
 
Lemma stepp_sameExec:
 forall (r1 r2 : State), stepp r1 r2 -> stepInv r1 ->  sameExec r1 r2.
Proof.
intros; induction H as [r|r1 r2 r3 H H1 HrecH].
unfold sameExec; intros; auto.
cut (sameExec r1 r2); [idtac | apply (step_sameExec r1); auto].
unfold sameExec; unfold sameExec in HrecH |-; intros.
rewrite H2; auto.
rewrite HrecH; auto.
apply (step_inv r1); auto.
intros x H5; apply H4.
generalize H5; (repeat rewrite getdst_app); intros; apply in_or_app.
elim
 (in_app_or
   (getdst (StateToMove r2) ++ getdst (StateBeing r2))
   (getdst (StateToMove r3) ++ getdst (StateBeing r3)) x); auto; intro.
generalize (step_inv_getdst r1 r2 x); (repeat rewrite getdst_app); intro.
left; apply H8; auto.
intros x H5; apply H4.
generalize H5; (repeat rewrite getdst_app); intros; apply in_or_app.
elim
 (in_app_or
   (getdst (StateToMove r1) ++ getdst (StateBeing r1))
   (getdst (StateToMove r2) ++ getdst (StateBeing r2)) x); auto; intro.
generalize (step_inv_getdst r1 r2 x); (repeat rewrite getdst_app); intro.
left; apply H8; auto.
Qed.
 
Inductive dstep : State -> State ->  Prop :=
  dstep_nop:
    forall (r : Reg) (t l : Moves),  dstep ((r, r) :: t, nil, l) (t, nil, l)
 | dstep_start:
     forall (t l : Moves) (s d : Reg),
     s <> d ->  dstep ((s, d) :: t, nil, l) (t, (s, d) :: nil, l)
 | dstep_push:
     forall (t1 t2 b l : Moves) (s d r : Reg),
     noRead t1 d ->
      dstep
       (t1 ++ ((d, r) :: t2), (s, d) :: b, l)
       (t1 ++ t2, (d, r) :: ((s, d) :: b), l)
 | dstep_pop_loop:
     forall (t b l : Moves) (s d r0 : Reg),
     noRead t r0 ->
      dstep
       (t, (s, r0) :: (b ++ ((r0, d) :: nil)), l)
       (t, b ++ ((T r0, d) :: nil), (s, r0) :: ((r0, T r0) :: l))
 | dstep_pop:
     forall (t b l : Moves) (s0 d0 sn dn : Reg),
     noRead t dn ->
     Loc.diff dn s0 ->
      dstep
       (t, (sn, dn) :: (b ++ ((s0, d0) :: nil)), l)
       (t, b ++ ((s0, d0) :: nil), (sn, dn) :: l)
 | dstep_last:
     forall (t l : Moves) (s d : Reg),
     noRead t d ->  dstep (t, (s, d) :: nil, l) (t, nil, (s, d) :: l) .
Hint Resolve dstep_nop dstep_start dstep_push .
Hint Resolve dstep_pop_loop dstep_pop dstep_last .
 
Lemma dstep_step:
 forall (r1 r2 : State), dstep r1 r2 -> stepInv r1 ->  stepp r1 r2.
Proof.
intros r1 r2 DS; inversion_clear DS; intros SI; eauto.
change (stepp (nil ++ ((r, r) :: t), nil, l) (t, nil, l)); apply step_stepp;
 apply (step_nop r nil t).
change (stepp (nil ++ ((s, d) :: t), nil, l) (t, (s, d) :: nil, l));
 apply step_stepp; apply (step_start nil t l).
apply
 (stepp_trans
   (t, (s, r0) :: (b ++ ((r0, d) :: nil)), l)
   (t, (s, r0) :: (b ++ ((T r0, d) :: nil)), (r0, T r0) :: l)
   (t, b ++ ((T r0, d) :: nil), (s, r0) :: ((r0, T r0) :: l))); auto.
apply step_stepp; apply step_pop; auto.
unfold stepInv in SI |-; generalize SI; intros [X [Y [Z [U V]]]].
generalize V; unfold StateBeing, noTmpLast.
case (b ++ ((r0, d) :: nil)); auto.
intros m l0 [R1 [OK PP]]; auto.
Qed.
 
Lemma dstep_inv:
 forall (r1 r2 : State), dstep r1 r2 -> stepInv r1 ->  stepInv r2.
Proof.
intros.
apply (stepp_inv r1 r2); auto.
apply dstep_step; auto.
Qed.
 
Inductive dstepp : State -> State ->  Prop :=
  dstepp_refl: forall (r : State),  dstepp r r
 | dstepp_trans:
     forall (r1 r2 r3 : State), dstep r1 r2 -> dstepp r2 r3 ->  dstepp r1 r3 .
Hint Resolve dstepp_refl dstepp_trans .
 
Lemma dstepp_stepp:
 forall (s1 s2 : State), stepInv s1 -> dstepp s1 s2 ->  stepp s1 s2.
Proof.
intros; induction H0 as [r|r1 r2 r3 H0 H1 HrecH0]; auto.
apply (stepp_transitive r1 r2 r3); auto.
apply dstep_step; auto.
apply HrecH0; auto.
apply (dstep_inv r1 r2); auto.
Qed.
 
Lemma dstepp_sameExec:
 forall (r1 r2 : State), dstepp r1 r2 -> stepInv r1 ->  sameExec r1 r2.
Proof.
intros; apply stepp_sameExec; auto.
apply dstepp_stepp; auto.
Qed.
 
End pmov.

Fixpoint split_move' (m : Moves) (r : Reg) {struct m} :
 option ((Moves * Reg) * Moves) :=
 match m with
   (s, d) :: tail =>
     match diff_dec s r with
       right _ => Some (nil, d, tail)
      | left _ =>
          match split_move' tail r with
            Some ((t1, r2, t2)) => Some ((s, d) :: t1, r2, t2)
           | None => None
          end
     end
  | nil => None
 end.
 
Fixpoint split_move (m : Moves) (r : Reg) {struct m} :
 option ((Moves * Reg) * Moves) :=
 match m with
   (s, d) :: tail =>
     match Loc.eq s r with
       left _ => Some (nil, d, tail)
      | right _ =>
          match split_move tail r with
            Some ((t1, r2, t2)) => Some ((s, d) :: t1, r2, t2)
           | None => None
          end
     end
  | nil => None
 end.

Definition def : Move := (R IT1, R IT1).
 
Fixpoint last (M : Moves) : Move :=
 match M with   nil => def
               | m :: nil => m
               | m :: tail => last tail end.
 
Fixpoint head_but_last (M : Moves) : Moves :=
 match M with
   nil => nil
  | m' :: nil => nil
  | m' :: tail => m' :: head_but_last tail
 end.
 
Fixpoint replace_last_s (M : Moves) : Moves :=
 match M with
   nil => nil
  | m :: nil =>
      match m with   (s, d) => (T s, d) :: nil end
  | m :: tail => m :: replace_last_s tail
 end.
 
Ltac CaseEq name := generalize (refl_equal name); pattern name at -1; case name.
 
Definition stepf' (S1 : State) : State :=
   match S1 with
     (nil, nil, _) => S1
    | ((s, d) :: tl, nil, l) =>
        match diff_dec s d with
          right _ => (tl, nil, l)
         | left _ => (tl, (s, d) :: nil, l)
        end
    | (t, (s, d) :: b, l) =>
        match split_move t d with
          Some ((t1, r, t2)) =>
            (t1 ++ t2, (d, r) :: ((s, d) :: b), l)
         | None =>
             match b with
               nil => (t, nil, (s, d) :: l)
              | _ =>
                  match diff_dec d (fst (last b)) with
                    right _ =>
                      (t, replace_last_s b, (s, d) :: ((d, T d) :: l))
                   | left _ => (t, b, (s, d) :: l)
                  end
             end
        end
   end.
 
Definition stepf (S1 : State) : State :=
   match S1 with
     (nil, nil, _) => S1
    | ((s, d) :: tl, nil, l) =>
        match Loc.eq s d with
          left _ => (tl, nil, l)
         | right _ => (tl, (s, d) :: nil, l)
        end
    | (t, (s, d) :: b, l) =>
        match split_move t d with
          Some ((t1, r, t2)) =>
            (t1 ++ t2, (d, r) :: ((s, d) :: b), l)
         | None =>
             match b with
               nil => (t, nil, (s, d) :: l)
              | _ =>
                  match Loc.eq d (fst (last b)) with
                    left _ =>
                      (t, replace_last_s b, (s, d) :: ((d, T d) :: l))
                   | right _ => (t, b, (s, d) :: l)
                  end
             end
        end
   end.
 
Lemma rebuild_l:
 forall (l : Moves) (m : Move),
  m :: l = head_but_last (m :: l) ++ (last (m :: l) :: nil).
Proof.
induction l; simpl; auto.
intros m; rewrite (IHl a); auto.
Qed.
 
Lemma splitSome:
 forall (l t1 t2 : Moves) (s d r : Reg),
 noOverlap (l ++ ((r, s) :: nil)) ->
 split_move l s = Some (t1, d, t2) ->  noRead t1 s.
Proof.
induction l; simpl.
intros; discriminate.
destruct a as [a1 a2].
intros t1 t2 s d r Hno; case (Loc.eq a1 s).
intros e H1; inversion H1.
simpl; auto.
CaseEq (split_move l s).
intros; (repeat destruct p).
inversion H0; auto.
simpl; split; auto.
change (noOverlap (((a1, a2) :: l) ++ ((r, s) :: nil))) in Hno |-.
assert (noOverlap ((r, s) :: ((a1, a2) :: l))).
apply noOverlap_Front0; auto.
unfold noOverlap in H1 |-; simpl in H1 |-.
elim H1 with ( l0 := a1 );
 [intros H5 H6; (try clear H1); (try exact H5) | idtac].
elim H5; [intros H1; (try clear H5); (try exact H1) | intros H1; (try clear H5)].
absurd (a1 = s); auto.
apply Loc.diff_sym; auto.
right; left; trivial.
apply (IHl m0 m s r0 r); auto.
apply (noOverlap_pop (a1, a2)); auto.
intros; discriminate.
Qed.
 
Lemma unsplit_move:
 forall (l t1 t2 : Moves) (s d r : Reg),
 noOverlap (l ++ ((r, s) :: nil)) ->
 split_move l s = Some (t1, d, t2) ->  l = t1 ++ ((s, d) :: t2).
Proof.
induction l.
simpl; intros; discriminate.
intros t1 t2 s d r HnoO; destruct a as [a1 a2]; simpl; case (diff_dec a1 s);
 intro.
case (Loc.eq a1 s); intro.
absurd (Loc.diff a1 s); auto.
rewrite e; apply Loc.same_not_diff.
CaseEq (split_move l s); intros; (try discriminate).
(repeat destruct p); inversion H0.
rewrite app_cons; subst t2; subst d; rewrite (IHl m0 m s r0 r); auto.
apply (noOverlap_pop (a1, a2)); auto.
case (Loc.eq a1 s); intros e H; inversion H; simpl.
rewrite e; auto.
cut (noOverlap_aux a1 (getdst ((r, s) :: nil))).
intros [[H5|H4] H0]; [try exact H5 | idtac].
absurd (s = a1); auto.
absurd (Loc.diff a1 s); auto; apply Loc.diff_sym; auto.
generalize HnoO; rewrite app_cons; intro.
assert (noOverlap (l ++ ((a1, a2) :: ((r, s) :: nil))));
 (try (apply noOverlap_insert; assumption)).
assert (noOverlap ((a1, a2) :: ((r, s) :: nil))).
apply (noOverlap_right l); auto.
generalize H2; unfold noOverlap; simpl.
intros H5; elim (H5 a1); [idtac | left; trivial].
intros H6 [[H7|H8] H9].
absurd (s = a1); auto.
split; [right; (try assumption) | auto].
Qed.
 
Lemma cons_replace:
 forall (a : Move) (l : Moves),
 l <> nil ->  replace_last_s (a :: l) = a :: replace_last_s l.
Proof.
intros; simpl.
CaseEq l.
intro; contradiction.
intros m l0 H0; auto.
Qed.
 
Lemma last_replace:
 forall (l : Moves) (s d : Reg),
  replace_last_s (l ++ ((s, d) :: nil)) = l ++ ((T s, d) :: nil).
Proof.
induction l; (try (simpl; auto; fail)).
intros; (repeat rewrite <- app_comm_cons).
rewrite cons_replace.
rewrite IHl; auto.
red; intro.
elim (app_eq_nil l ((s, d) :: nil)); auto; intros; discriminate.
Qed.
 
Lemma last_app: forall (l : Moves) (m : Move),  last (l ++ (m :: nil)) = m.
Proof.
induction l; simpl; auto.
intros m; CaseEq (l ++ (m :: nil)).
intro; elim (app_eq_nil l (m :: nil)); auto; intros; discriminate.
intros m0 l0 H; (rewrite <- H; apply IHl).
Qed.
 
Lemma last_cons:
 forall (l : Moves) (m m0 : Move),  last (m0 :: (m :: l)) = last (m :: l).
Proof.
intros; simpl; auto.
Qed.
 
Lemma stepf_popLoop:
 forall (t b l : Moves) (s d r0 : Reg),
 split_move t d = None ->
  stepf (t, (s, d) :: (b ++ ((d, r0) :: nil)), l) =
  (t, b ++ ((T d, r0) :: nil), (s, d) :: ((d, T d) :: l)).
Proof.
intros; simpl; rewrite H; CaseEq (b ++ ((d, r0) :: nil)); intros.
destruct b; discriminate.
rewrite <- H0; rewrite last_app; simpl; rewrite last_replace.
case (Loc.eq d d); intro; intuition.
destruct t; (try destruct m0); simpl; auto.
Qed.
 
Lemma stepf_pop:
 forall (t b l : Moves) (s d r r0 : Reg),
 split_move t d = None ->
 d <> r ->
  stepf (t, (s, d) :: (b ++ ((r, r0) :: nil)), l) =
  (t, b ++ ((r, r0) :: nil), (s, d) :: l).
Proof.
intros; simpl; rewrite H; CaseEq (b ++ ((r, r0) :: nil)); intros.
destruct b; discriminate.
rewrite <- H1; rewrite last_app; simpl.
case (Loc.eq d r); intro.
absurd (d = r); auto.
destruct t; (try destruct m0); simpl; auto.
Qed.
 
Lemma noOverlap_head:
 forall l1 l2 m, noOverlap (l1 ++ (m :: l2)) ->  noOverlap (l1 ++ (m :: nil)).
Proof.
induction l2; simpl; auto.
intros; apply IHl2.
cut (l1 ++ (m :: (a :: l2)) = (l1 ++ (m :: nil)) ++ (a :: l2));
 [idtac | rewrite app_ass; auto].
intros e; rewrite e in H.
cut (l1 ++ (m :: l2) = (l1 ++ (m :: nil)) ++ l2);
 [idtac | rewrite app_ass; auto].
intros e'; rewrite e'; auto.
apply noOverlap_Pop with a; auto.
Qed.
 
Lemma splitNone:
 forall (l : Moves) (s d : Reg),
 split_move l d = None -> noOverlap (l ++ ((s, d) :: nil)) ->  noRead l d.
Proof.
induction l; intros s d; simpl; auto.
destruct a as [a1 a2]; case (Loc.eq a1 d); intro; (try (intro; discriminate)).
CaseEq (split_move l d); intros.
(repeat destruct p); discriminate.
split; (try assumption).
change (noOverlap (((a1, a2) :: l) ++ ((s, d) :: nil))) in H1 |-.
assert (noOverlap ((s, d) :: ((a1, a2) :: l))).
apply noOverlap_Front0; auto.
assert (noOverlap ((a1, a2) :: ((s, d) :: l))).
apply noOverlap_swap; auto.
unfold noOverlap in H3 |-; simpl in H3 |-.
elim H3 with ( l0 := a1 );
 [intros H5 H6; (try clear H1); (try exact H5) | idtac].
elim H6;
 [intros H1 H4; elim H1;
   [intros H7; (try clear H1 H6); (try exact H7) | intros H7; (try clear H1 H6)]].
absurd (a1 = d); auto.
apply Loc.diff_sym; auto.
left; trivial.
apply IHl with s; auto.
apply noOverlap_pop with (a1, a2); auto.
Qed.
 
Lemma noO_diff:
 forall l1 l2 s d r r0,
 noOverlap (l1 ++ ((s, d) :: (l2 ++ ((r, r0) :: nil)))) ->
  r = d \/ Loc.diff d r.
Proof.
intros.
assert (noOverlap ((s, d) :: (l2 ++ ((r, r0) :: nil)))); auto.
apply (noOverlap_right l1); auto.
assert (noOverlap ((l2 ++ ((r, r0) :: nil)) ++ ((s, d) :: nil))); auto.
apply (noOverlap_movBack0 (l2 ++ ((r, r0) :: nil))); auto.
assert
 ((l2 ++ ((r, r0) :: nil)) ++ ((s, d) :: nil) =
  l2 ++ (((r, r0) :: nil) ++ ((s, d) :: nil))); auto.
rewrite app_ass; auto.
rewrite H2 in H1.
simpl in H1 |-.
assert (noOverlap ((r, r0) :: ((s, d) :: nil))); auto.
apply (noOverlap_right l2); auto.
unfold noOverlap in H3 |-.
generalize (H3 r); simpl.
intros H4; elim H4; intros; [idtac | left; trivial].
elim H6; intros [H9|H9] H10; [left | right]; auto.
Qed.
 
Lemma f2ind:
 forall (S1 S2 : State),
 (forall (l : Moves),  (S1 <> (nil, nil, l))) ->
 noOverlap (StateToMove S1 ++ StateBeing S1) -> stepf S1 = S2 ->  dstep S1 S2.
Proof.
intros S1 S2 Hneq HnoO; destruct S1 as [[t b] l]; destruct b.
destruct t.
elim (Hneq l); auto.
destruct m; simpl; case (Loc.eq r r0).
intros.
rewrite e; rewrite <- H; apply dstep_nop.
intros n H; rewrite <- H; generalize (dstep_start t l r r0); auto.
intros H; rewrite <- H; destruct m as [s d].
CaseEq (split_move t d).
intros p H0; destruct p as [[t1 s0] t2]; simpl; rewrite H0; destruct t; simpl.
simpl in H0 |-; discriminate.
rewrite (unsplit_move (m :: t) t1 t2 d s0 s); auto.
destruct m; generalize dstep_push; intros H1; apply H1.
unfold StateToMove, StateBeing in HnoO |-.
apply (splitSome ((r, r0) :: t) t1 t2 d s0 s); auto.
apply noOverlap_head with b; auto.
unfold StateToMove, StateBeing in HnoO |-.
apply noOverlap_head with b; auto.
intros H0; destruct b.
simpl.
rewrite H0.
destruct t; (try destruct m); generalize dstep_last; intros H1; apply H1.
simpl; auto.
unfold StateToMove, StateBeing in HnoO |-.
apply splitNone with s; auto.
unfold StateToMove, StateBeing in HnoO |-.
generalize HnoO; clear HnoO; rewrite (rebuild_l b m); intros HnoO.
destruct (last (m :: b)).
case (Loc.eq d r).
intros e; rewrite <- e.
CaseEq (head_but_last (m :: b)); intros; [simpl | idtac];
 (try
   (destruct t; (try destruct m0); rewrite H0;
     (case (Loc.eq d d); intros h; (try (elim h; auto))))).
generalize (dstep_pop_loop nil nil); simpl; intros H3; apply H3; auto.
generalize (dstep_pop_loop ((r1, r2) :: t) nil); unfold T; simpl app;
 intros H3; apply H3; clear H3; apply splitNone with s; (try assumption).
apply noOverlap_head with (head_but_last (m :: b) ++ ((r, r0) :: nil)); auto.
rewrite stepf_popLoop; auto.
generalize (dstep_pop_loop t (m0 :: l0)); simpl; intros H3; apply H3; clear H3;
 apply splitNone with s; (try assumption).
apply noOverlap_head with (head_but_last (m :: b) ++ ((r, r0) :: nil)); auto.
intro; assert (Loc.diff d r).
assert (r = d \/ Loc.diff d r).
apply (noO_diff t (head_but_last (m :: b)) s d r r0); auto.
elim H1; [intros H2; absurd (d = r); auto | intros H2; auto].
rewrite stepf_pop; auto.
generalize (dstep_pop t (head_but_last (m :: b))); intros H3; apply H3; auto.
clear H3; apply splitNone with s; (try assumption).
apply noOverlap_head with (head_but_last (m :: b) ++ ((r, r0) :: nil)); auto.
Qed.
 
Lemma f2ind':
 forall (S1 : State),
 (forall (l : Moves),  (S1 <> (nil, nil, l))) ->
 noOverlap (StateToMove S1 ++ StateBeing S1) ->  dstep S1 (stepf S1).
Proof.
intros S1 H noO; apply f2ind; auto.
Qed.
 
Lemma appcons_length:
 forall (l1 l2 : Moves) (m : Move),
  length (l1 ++ (m :: l2)) = (length (l1 ++ l2) + 1%nat)%nat.
Proof.
induction l1; simpl; intros; [omega | idtac].
rewrite IHl1; omega.
Qed.
 
Definition mesure (S0 : State) : nat :=
   let (p, _) := S0 in let (t, b) := p in (2 * length t + length b)%nat.
 
Lemma step_dec0:
 forall (t1 t2 b1 b2 : Moves) (l1 l2 : Moves),
 dstep (t1, b1, l1) (t2, b2, l2) ->
  (2 * length t2 + length b2 < 2 * length t1 + length b1)%nat.
Proof.
intros t1 t2 b1 b2 l1 l2 H; inversion H; simpl; (try omega).
rewrite appcons_length; omega.
cut (length (b ++ ((T r0, d) :: nil)) = length (b ++ ((r0, d) :: nil)));
 (try omega).
induction b; simpl; auto.
(repeat rewrite appcons_length); auto.
Qed.
 
Lemma step_dec:
 forall (S1 S2 : State), dstep S1 S2 ->  (mesure S2 < mesure S1)%nat.
Proof.
unfold mesure; destruct S1 as [[t1 b1] l1]; destruct S2 as [[t2 b2] l2].
intro; apply (step_dec0 t1 t2 b1 b2 l1 l2); trivial.
Qed.
 
Lemma stepf_dec0:
 forall (S1 S2 : State),
 (forall (l : Moves),  (S1 <> (nil, nil, l))) /\
 (S2 = stepf S1 /\ noOverlap (StateToMove S1 ++ StateBeing S1)) ->
  (mesure S2 < mesure S1)%nat.
Proof.
intros S1 S2 [H1 [H2 H3]]; apply step_dec.
apply f2ind; trivial.
rewrite H2; reflexivity.
Qed.
 
Lemma stepf_dec:
 forall (S1 S2 : State),
 S2 = stepf S1 /\
 ((forall (l : Moves),  (S1 <> (nil, nil, l))) /\
  noOverlap (StateToMove S1 ++ StateBeing S1)) ->  ltof _ mesure S2 S1.
Proof.
unfold ltof.
intros S1 S2 [H1 [H2 H3]]; apply step_dec.
apply f2ind; trivial.
rewrite H1; reflexivity.
Qed.
 
Lemma replace_last_id:
 forall l m m0,  replace_last_s (m :: (m0 :: l)) = m :: replace_last_s (m0 :: l).
Proof.
intros; case l; simpl.
destruct m0; simpl; auto.
intros; case l0; auto.
Qed.
 
Lemma length_replace: forall l,  length (replace_last_s l) = length l.
Proof.
induction l; simpl; auto.
destruct l; destruct a; simpl; auto.
Qed.
 
Lemma length_app:
 forall (A : Set) (l1 l2 : list A),
  (length (l1 ++ l2) = length l1 + length l2)%nat.
Proof.
intros A l1 l2; (try assumption).
induction l1; simpl; auto.
Qed.
 
Lemma split_length:
 forall (l t1 t2 : Moves) (s d : Reg),
 split_move l s = Some (t1, d, t2) ->
  (length l = (length t1 + length t2) + 1)%nat.
Proof.
induction l.
intros; discriminate.
intros t1 t2 s d; destruct a as [r r0]; simpl; case (Loc.eq r s); intro.
intros H; inversion H.
simpl; omega.
CaseEq (split_move l s); (try (intros; discriminate)).
(repeat destruct p); intros H H0; inversion H0.
rewrite H2; rewrite (IHl m0 m s r1); auto.
rewrite H4; rewrite <- H2; simpl; omega.
Qed.
 
Lemma stepf_dec0':
 forall (S1 : State),
 (forall (l : Moves),  (S1 <> (nil, nil, l))) ->
  (mesure (stepf S1) < mesure S1)%nat.
Proof.
intros S1 H.
unfold mesure; destruct S1 as [[t1 b1] l1].
destruct t1.
destruct b1.
generalize (H l1); intros H1; elim H1; auto.
destruct m; simpl.
destruct b1.
simpl; auto.
case (Loc.eq r0 (fst (last (m :: b1)))).
intros; rewrite length_replace; simpl; omega.
simpl; case b1; intros; simpl; omega.
destruct m.
destruct b1.
simpl.
case (Loc.eq r r0); intros; simpl; omega.
destruct m; simpl; case (Loc.eq r r2).
intros; simpl; omega.
CaseEq (split_move t1 r2); intros.
destruct p; destruct p; simpl.
rewrite (split_length t1 m0 m r2 r3); auto.
rewrite length_app; auto.
omega.
destruct b1.
simpl; omega.
case (Loc.eq r2 (fst (last (m :: b1)))); intros.
rewrite length_replace; simpl; omega.
simpl; omega.
Qed.
 
Lemma stepf1_dec:
 forall (S1 S2 : State),
 (forall (l : Moves),  (S1 <> (nil, nil, l))) ->
 S2 = stepf S1 ->  ltof _ mesure S2 S1.
Proof.
unfold ltof; intros S1 S2 H H0; rewrite H0.
apply stepf_dec0'; (try assumption).
Qed.
 
Lemma disc1:
 forall (a : Move) (l1 l2 l3 l4 : list Move),
  ((a :: l1, l2, l3) <> (nil, nil, l4)).
Proof.
intros; discriminate.
Qed.
 
Lemma disc2:
 forall (a : Move) (l1 l2 l3 l4 : list Move),
  ((l1, a :: l2, l3) <> (nil, nil, l4)).
Proof.
intros; discriminate.
Qed.
Hint Resolve disc1 disc2 .
 
Lemma sameExec_reflexive: forall (r : State),  sameExec r r.
Proof.
intros r; unfold sameExec, sameEnv, exec.
destruct r as [[t b] d]; trivial.
Qed.
 
Definition base_case_Pmov_dec:
 forall (s : State),
  ({ exists l : list Move , s = (nil, nil, l)  }) +
  ({ forall l,  (s <> (nil, nil, l)) }).
Proof.
destruct s as [[[|x tl] [|y tl']] l]; (try (right; intro; discriminate)).
left; exists l; auto.
Defined.
 
Definition Pmov :=
   Fix
    (well_founded_ltof _ mesure) (fun _ => State)
    (fun (S1 : State) =>
     fun (Pmov : forall x, ltof _ mesure x S1 ->  State) =>
        match base_case_Pmov_dec S1 with
          left h => S1
         | right h => Pmov (stepf S1) (stepf_dec0' S1 h) end).
 
Theorem Pmov_equation: forall S1,  Pmov S1 = match S1 with
                                               ((nil, nil), _) => S1
                                              | _ => Pmov (stepf S1)
                                             end.
Proof.
intros S1; unfold Pmov at 1;
 rewrite (Fix_eq
           (well_founded_ltof _ mesure) (fun _ => State)
           (fun (S1 : State) =>
            fun (Pmov : forall x, ltof _ mesure x S1 ->  State) =>
               match base_case_Pmov_dec S1 with
                 left h => S1
                | right h => Pmov (stepf S1) (stepf_dec0' S1 h) end)).
fold Pmov.
destruct S1 as [[[|x tl] [|y tl']] l];
 match goal with
 | |- match ?a with left _ => _ | right _ => _ end = _ => case a end;
 (try (intros [l0 Heq]; discriminate Heq)); auto.
intros H; elim (H l); auto.
intros x f g Hfg_ext.
match goal with
| |- match ?a with left _ => _ | right _ => _ end = _ => case a end; auto.
Qed.
 
Lemma sameExec_transitive:
 forall (r1 r2 r3 : State),
 (forall r,
  In r (getdst (StateToMove r2 ++ StateBeing r2)) ->
   In r (getdst (StateToMove r1 ++ StateBeing r1))) ->
 (forall r,
  In r (getdst (StateToMove r3 ++ StateBeing r3)) ->
   In r (getdst (StateToMove r2 ++ StateBeing r2))) ->
 sameExec r1 r2 -> sameExec r2 r3 ->  sameExec r1 r3.
Proof.
intros r1 r2 r3; unfold sameExec, exec; (repeat rewrite getdst_app).
destruct r1 as [[t1 b1] d1]; destruct r2 as [[t2 b2] d2];
 destruct r3 as [[t3 b3] d3]; simpl.
intros Hin; intros.
rewrite H0; auto.
rewrite H1; auto.
intros.
apply (H3 x).
apply in_or_app; auto.
elim (in_app_or (getdst t2 ++ getdst b2) (getdst t3 ++ getdst b3) x); auto.
intros.
apply (H3 x).
apply in_or_app; auto.
elim (in_app_or (getdst t1 ++ getdst b1) (getdst t2 ++ getdst b2) x); auto.
Qed.
 
Lemma dstep_inv_getdst:
 forall (s1 s2 : State) r,
 dstep s1 s2 ->
 In r (getdst (StateToMove s2 ++ StateBeing s2)) ->
  In r (getdst (StateToMove s1 ++ StateBeing s1)).
intros s1 s2 r STEP; inversion_clear STEP;
 unfold StateToMove, StateBeing, StateDone; (repeat rewrite app_nil);
 (repeat (rewrite getdst_app; simpl)); intro; auto.
Proof.
right; (try assumption).
elim (in_app_or (getdst t) (d :: nil) r); auto; (simpl; intros [H1|H1]);
 [left; assumption | inversion H1].
elim (in_app_or (getdst t1 ++ getdst t2) (r0 :: (d :: getdst b)) r); auto;
 (simpl; intros).
elim (in_app_or (getdst t1) (getdst t2) r); auto; (simpl; intros).
apply in_or_app; left; apply in_or_app; left; assumption.
apply in_or_app; left; apply in_or_app; right; simpl; right; assumption.
elim H1; [intros H2 | intros [H2|H2]].
apply in_or_app; left; apply in_or_app; right; simpl; left; auto.
apply in_or_app; right; simpl; left; auto.
apply in_or_app; right; simpl; right; assumption.
elim (in_app_or (getdst t) (getdst b ++ (d :: nil)) r); auto; (simpl; intros).
apply in_or_app; left; assumption.
elim (in_app_or (getdst b) (d :: nil) r); auto; (simpl; intros).
apply in_or_app; right; simpl; right; apply in_or_app; left; assumption.
elim H2; [intros H3 | intros H3; inversion H3].
apply in_or_app; right; simpl; right; apply in_or_app; right; simpl; auto.
elim (in_app_or (getdst t) (getdst b ++ (d0 :: nil)) r); auto; (simpl; intros).
apply in_or_app; left; assumption.
elim (in_app_or (getdst b) (d0 :: nil) r); auto; simpl;
 [intros H3 | intros [H3|H3]; [idtac | inversion H3]].
apply in_or_app; right; simpl; right; apply in_or_app; left; assumption.
apply in_or_app; right; simpl; right; apply in_or_app; right; simpl; auto.
apply in_or_app; left; assumption.
Qed.
 
Theorem STM_Pmov: forall (S1 : State),  StateToMove (Pmov S1) = nil.
Proof.
intros S1; elim S1  using (well_founded_ind (Wf_nat.well_founded_ltof _ mesure)).
clear S1; intros S1; intros Hrec; destruct S1 as [[t b] d];
 rewrite Pmov_equation; destruct t.
destruct b; auto.
apply Hrec; apply stepf1_dec; auto.
apply Hrec; apply stepf1_dec; auto.
Qed.
 
Theorem SB_Pmov: forall (S1 : State),  StateBeing (Pmov S1) = nil.
Proof.
intros S1; elim S1  using (well_founded_ind (Wf_nat.well_founded_ltof _ mesure)).
clear S1; intros S1; intros Hrec; destruct S1 as [[t b] d];
 rewrite Pmov_equation; destruct t.
destruct b; auto.
apply Hrec; apply stepf1_dec; auto.
apply Hrec; apply stepf1_dec; auto.
Qed.
 
Theorem Fpmov_correct:
 forall (S1 : State), stepInv S1 ->  sameExec S1 (Pmov S1).
Proof.
intros S1; elim S1  using (well_founded_ind (Wf_nat.well_founded_ltof _ mesure)).
clear S1; intros S1; intros Hrec Hinv; rewrite Pmov_equation;
 destruct S1 as [[t b] d].
assert
 (forall (r : Reg) S1,
  In r (getdst (StateToMove (Pmov (stepf S1)) ++ StateBeing (Pmov (stepf S1)))) ->
   In r (getdst (StateToMove (stepf S1) ++ StateBeing (stepf S1)))).
intros r S1; rewrite (STM_Pmov (stepf S1)); rewrite SB_Pmov; simpl; intros.
inversion H.
destruct t.
destruct b.
apply sameExec_reflexive.
set (S1:=(nil (A:=Move), m :: b, d)).
assert (dstep S1 (stepf S1)); (try apply f2ind); unfold S1; auto.
elim Hinv; intros Hpath [SD [NO NT]]; assumption.
apply sameExec_transitive with (stepf S1); auto.
intros r; apply dstep_inv_getdst; auto.
apply dstepp_sameExec; auto; apply dstepp_trans with (stepf S1); auto.
apply dstepp_refl; auto.
apply Hrec; auto.
unfold ltof; apply step_dec; assumption.
apply (dstep_inv S1); assumption.
set (S1:=(m :: t, b, d)).
assert (dstep S1 (stepf S1)); (try apply f2ind); unfold S1; auto.
elim Hinv; intros Hpath [SD [NO NT]]; assumption.
apply sameExec_transitive with (stepf S1); auto.
intros r; apply dstep_inv_getdst; auto.
apply dstepp_sameExec; auto; apply dstepp_trans with (stepf S1); auto.
apply dstepp_refl; auto.
apply Hrec; auto.
unfold ltof; apply step_dec; assumption.
apply (dstep_inv S1); assumption.
Qed.
 
Definition P_move := fun (p : Moves) => StateDone (Pmov (p, nil, nil)).
 
Definition Sexec := sexec.
 
Definition Get := get.
 
Fixpoint listsLoc2Moves (src dst : list loc) {struct src} : Moves :=
 match src with
   nil => nil
  | s :: srcs =>
      match dst with
        nil => nil
       | d :: dsts => (s, d) :: listsLoc2Moves srcs dsts
      end
 end.
 
Definition no_overlap (l1 l2 : list loc) :=
   forall r, In r l1 -> forall s, In s l2 ->  r = s \/ Loc.diff r s.
 
Definition no_overlap_state (S : State) :=
   no_overlap
    (getsrc (StateToMove S ++ StateBeing S))
    (getdst (StateToMove S ++ StateBeing S)).
 
Definition no_overlap_list := fun l => no_overlap (getsrc l) (getdst l).
 
Lemma Indst_noOverlap_aux:
 forall l1 l,
 (forall (s : Reg), In s (getdst l1) ->  l = s \/ Loc.diff l s) ->
  noOverlap_aux l (getdst l1).
Proof.
intros; induction l1; simpl; auto.
destruct a as [a1 a2]; simpl; split.
elim (H a2); (try intros H0).
left; auto.
right; apply Loc.diff_sym; auto.
simpl; left; trivial.
apply IHl1; intros.
apply H; simpl; right; (try assumption).
Qed.
 
Lemma no_overlap_noOverlap:
 forall r, no_overlap_state r ->  noOverlap (StateToMove r ++ StateBeing r).
Proof.
intros r; unfold noOverlap, no_overlap_state.
set (l1:=StateToMove r ++ StateBeing r).
unfold no_overlap; intros H l H0.
apply Indst_noOverlap_aux; intros; apply H; auto.
Qed.
 
Theorem Fpmov_correctMoves:
 forall p e r,
 simpleDest p ->
 no_overlap_list p ->
 noTmp p ->
 notemporary r ->
 (forall (x : Reg), In x (getdst p) ->  r = x \/ Loc.diff r x) ->
  get (pexec p e) r = get (sexec (StateDone (Pmov (p, nil, nil))) e) r.
Proof.
intros p e r SD no_O notmp notempo.
generalize (Fpmov_correct (p, nil, nil)); unfold sameExec, exec; simpl;
 rewrite SB_Pmov; rewrite STM_Pmov; simpl.
(repeat rewrite app_nil); intro.
apply H; auto.
unfold stepInv; simpl; (repeat split); (try (rewrite app_nil; assumption)); auto.
generalize (no_overlap_noOverlap (p, nil, nil)); simpl; intros; auto.
apply H0; auto; unfold no_overlap_list in H0 |-.
unfold no_overlap_state; simpl; (repeat rewrite app_nil); auto.
Qed.
 
Theorem Fpmov_correct1:
 forall (p : Moves) (e : Env) (r : Reg),
 simpleDest p ->
 no_overlap_list p ->
 noTmp p ->
 notemporary r ->
 (forall (x : Reg), In x (getdst p) ->  r = x \/ Loc.diff r x) ->
 noWrite p r ->  get e r = get (sexec (StateDone (Pmov (p, nil, nil))) e) r.
Proof.
intros p e r Hsd Hno_O HnoTmp Hrnotempo Hrno_Overlap Hnw.
rewrite <- (Fpmov_correctMoves p e); (try assumption).
destruct p; auto.
destruct m as [m1 m2]; simpl; case (Loc.eq m2 r); intros.
elim Hnw; intros; absurd (Loc.diff m2 r); auto.
rewrite e0; apply Loc.same_not_diff.
elim Hnw; intros H1 H2.
rewrite get_update_diff; (try assumption).
apply get_noWrite; (try assumption).
Qed.
 
Lemma In_SD_diff:
 forall (s d a1 a2 : Reg) (p : Moves),
 In (s, d) p -> simpleDest ((a1, a2) :: p) ->  Loc.diff a2 d.
Proof.
intros; induction p.
inversion H.
elim H; auto.
intro; subst a; elim H0; intros H1 H2; elim H1; intros; apply Loc.diff_sym;
 assumption.
intro; apply IHp; auto.
apply simpleDest_pop2 with a; (try assumption).
Qed.
 
Theorem pexec_correct:
 forall (e : Env) (m : Move) (p : Moves),
 In m p -> simpleDest p ->  (let (s, d) := m in get (pexec p e) d = get e s).
Proof.
induction p; intros.
elim H.
destruct m.
elim (in_inv H); intro.
rewrite H1; simpl; rewrite get_update_id; auto.
destruct a as [a1 a2]; simpl.
rewrite get_update_diff.
apply IHp; auto.
apply (simpleDest_pop (a1, a2)); (try assumption).
apply (In_SD_diff r) with ( p := p ) ( a1 := a1 ); auto.
Qed.
 
Lemma In_noTmp_notempo:
 forall (s d : Reg) (p : Moves), In (s, d) p -> noTmp p ->  notemporary d.
Proof.
intros; unfold notemporary; induction p.
inversion H.
elim H; intro.
subst a; elim H0; intros H1 [H3 H2]; (try assumption).
intro; apply IHp; auto.
destruct a; elim H0; intros _ [H2 H3]; (try assumption).
Qed.
 
Lemma In_Indst: forall s d p, In (s, d) p ->  In d (getdst p).
Proof.
intros; induction p; auto.
destruct a; simpl.
elim H; intro.
left; inversion H0; trivial.
right; apply IHp; auto.
Qed.
 
Lemma In_SD_diff':
 forall (d a1 a2 : Reg) (p : Moves),
 In d (getdst p) -> simpleDest ((a1, a2) :: p) ->  Loc.diff a2 d.
Proof.
intros d a1 a2 p H H0; induction p.
inversion H.
destruct a; elim H.
elim H0; simpl; intros.
subst r0.
elim H1; intros H3 H4; apply Loc.diff_sym; assumption.
intro; apply IHp; (try assumption).
apply simpleDest_pop2 with (r, r0); (try assumption).
Qed.
 
Lemma In_SD_no_o:
 forall (s d : Reg) (p : Moves),
 In (s, d) p ->
 simpleDest p -> forall (x : Reg), In x (getdst p) ->  d = x \/ Loc.diff d x.
Proof.
intros s d p Hin Hsd; induction p.
inversion Hin.
destruct a as [a1 a2]; elim Hin; intros.
inversion H; subst d; subst s.
elim H0; intros H1; [left | right]; (try assumption).
apply (In_SD_diff' x a1 a2 p); auto.
elim H0.
intro; subst x.
right; apply Loc.diff_sym; apply (In_SD_diff s d a1 a2 p); auto.
intro; apply IHp; auto.
apply (simpleDest_pop (a1, a2)); assumption.
Qed.
 
Lemma getdst_map: forall p,  getdst p = map (fun x => snd x) p.
Proof.
induction p.
simpl; auto.
destruct a; simpl.
rewrite IHp; auto.
Qed.
 
Lemma getsrc_map: forall p,  getsrc p = map (fun x => fst x) p.
Proof.
induction p.
simpl; auto.
destruct a; simpl.
rewrite IHp; auto.
Qed.
 
Theorem Fpmov_correct2:
 forall (p : Moves) (e : Env) (m : Move),
 In m p ->
 simpleDest p ->
 no_overlap_list p ->
 noTmp p ->
  (let (s, d) := m in get (sexec (StateDone (Pmov (p, nil, nil))) e) d = get e s).
Proof.
intros p e m Hin Hsd Hno_O HnoTmp; destruct m as [s d];
 generalize (Fpmov_correctMoves p e); intros.
rewrite <- H; auto.
apply pexec_correct with ( m := (s, d) ); auto.
apply (In_noTmp_notempo s d p); auto.
apply (In_SD_no_o s d p Hin Hsd).
Qed.
 
Lemma notindst_nW: forall a p, Loc.notin a (getdst p) ->  noWrite p a.
Proof.
induction p; simpl; auto.
destruct a0 as [a1 a2].
simpl.
intros H; elim H; intro; split.
apply Loc.diff_sym; (try assumption).
apply IHp; auto.
Qed.
 
Lemma disjoint_tmp__noTmp:
 forall p,
 Loc.disjoint (getsrc p) temporaries ->
 Loc.disjoint (getdst p) temporaries ->  noTmp p.
Proof.
induction p; simpl; auto.
destruct a as [a1 a2]; simpl getsrc; simpl getdst; unfold Loc.disjoint; intros;
 (repeat split).
intro; unfold T; case (Loc.type r); apply H; (try (left; trivial; fail)).
right; left; trivial.
right; right; right; right; left; trivial.
intro; unfold T; case (Loc.type r); apply H0; (try (left; trivial; fail)).
right; left; trivial.
right; right; right; right; left; trivial.
apply IHp.
apply Loc.disjoint_cons_left with a1; auto.
apply Loc.disjoint_cons_left with a2; auto.
Qed.
 
Theorem Fpmov_correct_IT3:
 forall p rs,
 simpleDest p ->
 no_overlap_list p ->
 Loc.disjoint (getsrc p) temporaries ->
 Loc.disjoint (getdst p) temporaries ->
  (sexec (StateDone (Pmov (p, nil, nil))) rs) (R IT3) = rs (R IT3).
Proof.
intros p rs Hsd Hno_O Hdistmpsrc Hdistmpdst.
generalize (Fpmov_correctMoves p rs); unfold get, Locmap.get; intros H2.
rewrite <- H2; auto.
generalize (get_noWrite p (R IT3)); unfold get, Locmap.get; intros.
rewrite <- H; auto.
apply notindst_nW.
apply (Loc.disjoint_notin temporaries).
apply Loc.disjoint_sym; auto.
right; right; left; trivial.
apply disjoint_tmp__noTmp; auto.
unfold notemporary, T.
intros x; case (Loc.type x); simpl; intro; discriminate.
intros x H; right; apply Loc.in_notin_diff with (getdst p); auto.
apply Loc.disjoint_notin with temporaries; auto.
apply Loc.disjoint_sym; auto.
right; right; left; trivial.
Qed.
 
Theorem Fpmov_correct_map:
 forall p rs,
 simpleDest p ->
 no_overlap_list p ->
 Loc.disjoint (getsrc p) temporaries ->
 Loc.disjoint (getdst p) temporaries ->
  List.map (sexec (StateDone (Pmov (p, nil, nil))) rs) (getdst p) =
  List.map rs (getsrc p).
Proof.
intros; rewrite getsrc_map; rewrite getdst_map; rewrite list_map_compose;
 rewrite list_map_compose; apply list_map_exten; intros.
generalize (Fpmov_correct2 p rs x).
destruct x; simpl.
unfold get, Locmap.get; intros; auto.
rewrite H4; auto.
apply disjoint_tmp__noTmp; auto.
Qed.
 
Theorem Fpmov_correct_ext:
 forall p rs,
 simpleDest p ->
 no_overlap_list p ->
 Loc.disjoint (getsrc p) temporaries ->
 Loc.disjoint (getdst p) temporaries ->
 forall l,
 Loc.notin l (getdst p) ->
 Loc.notin l temporaries ->
  (sexec (StateDone (Pmov (p, nil, nil))) rs) l = rs l.
Proof.
intros; generalize (Fpmov_correct1 p rs l); unfold get, Locmap.get; intros.
rewrite <- H5; auto.
apply disjoint_tmp__noTmp; auto.
unfold notemporary; simpl in H4 |-; unfold T; intros x; case (Loc.type x).
elim H4;
 [intros H6 H7; elim H7; [intros H8 H9; (try clear H7 H4); (try exact H8)]].
elim H4;
 [intros H6 H7; elim H7;
   [intros H8 H9; elim H9;
     [intros H10 H11; elim H11;
       [intros H12 H13; elim H13;
         [intros H14 H15; (try clear H13 H11 H9 H7 H4); (try exact H14)]]]]].
unfold no_overlap_list, no_overlap in H0 |-; intros.
case (Loc.eq l x).
intros e; left; (try assumption).
intros n; right; (try assumption).
apply Loc.in_notin_diff with (getdst p); auto.
apply notindst_nW; auto.
Qed.

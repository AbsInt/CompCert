Require Import InterfGraph.
Require Import AST.
Require Import FSets.
Require Import Locations.
Require Import Registers.

Module Import SRRFacts := Facts SetRegReg.
Module MRegset := FSetAVL.Make OrderedMreg.

Close Scope nat_scope.

Definition regregpartition : Type := SetRegReg.t*SetRegReg.t*Regset.t*Regset.t.

Definition rr1 := fun (p : regregpartition) => fst (fst (fst p)).
Definition rr2 := fun (p : regregpartition) => snd (fst (fst p)).
Definition rr3 := fun (p : regregpartition) => snd (fst p).
Definition rr4 := fun (p : regregpartition) => snd p.

Definition regreg_edge_type_partition s env :=
SetRegReg.fold (fun e s => match env (fst e), env (snd e) with
                           | Tint, Tint => (SetRegReg.add e (rr1 s), rr2 s,
                                                    Regset.add (fst e) (Regset.add (snd e) (rr3 s)), rr4 s)
                           | Tfloat, Tfloat => (rr1 s, SetRegReg.add e (rr2 s), rr3 s,
                                                     Regset.add (fst e) (Regset.add (snd e) (rr4 s)))
                           | Tint, Tfloat => (rr1 s, rr2 s, Regset.add (fst e) (rr3 s), Regset.add (snd e) (rr4 s))
                           | Tfloat, Tint => (rr1 s, rr2 s, Regset.add (snd e) (rr3 s), Regset.add (fst e) (rr4 s))
                           end)
               s
               (SetRegReg.empty, SetRegReg.empty, Regset.empty, Regset.empty).

Lemma in_partition_in_fst : forall e s env,
SetRegReg.In e (rr1 (regreg_edge_type_partition s env)) ->
SetRegReg.In e s.

Proof.
intros e s env H.
unfold regreg_edge_type_partition in H.
set (f := fun (e : SetRegReg.elt) (s : regregpartition) =>
             match env (fst e) with
             | Tint =>
                 match env (snd e) with
                 | Tint =>
                     (SetRegReg.add e (rr1 s), rr2 s,
                     Regset.add (fst e) (Regset.add (snd e) (rr3 s)), 
                     rr4 s)
                 | Tfloat =>
                     (rr1 s, rr2 s, Regset.add (fst e) (rr3 s),
                     Regset.add (snd e) (rr4 s))
                 end
             | Tfloat =>
                 match env (snd e) with
                 | Tint =>
                     (rr1 s, rr2 s, Regset.add (snd e) (rr3 s),
                     Regset.add (fst e) (rr4 s))
                 | Tfloat =>
                     (rr1 s, SetRegReg.add e (rr2 s), rr3 s,
                     Regset.add (fst e) (Regset.add (snd e) (rr4 s)))
                 end
             end).
unfold regregpartition in *. fold f in H.

assert (forall e set1 set2 set3 set4, SetRegReg.In e (rr1 (SetRegReg.fold f s (set1, set2, set3, set4))) ->
                         SetRegReg.In e s \/ SetRegReg.In e set1 \/ SetRegReg.In e set2).
clear H.
intros e' s1 s2 s3 s4 H.
rewrite SetRegReg.fold_1 in H.
generalize H. generalize s1 s2 s3 s4. clear s1 s2 s3 s4 H.
generalize (SetRegReg.elements_2). intro HH.
generalize (HH s). clear HH. intro HH.
induction (SetRegReg.elements s).
simpl. right. left. assumption.
intros s1 s2 s3 s4 H.
simpl in H.
assert ((forall x : SetRegReg.elt,
       SetoidList.InA (fun x0 y : OrderedRegReg.t => fst x0 = fst y /\ snd x0 = snd y) x l ->
       SetRegReg.In x s)).
intros. apply HH. right. assumption.
generalize (IHl H0). clear IHl H0. intro IHl.
assert (f a (s1, s2, s3, s4) = (SetRegReg.add a s1, s2, Regset.add (fst a) (Regset.add (snd a) s3), s4) \/
        f a (s1, s2, s3, s4) = (s1, SetRegReg.add a s2, s3, Regset.add (fst a) (Regset.add (snd a) s4)) \/
        f a (s1, s2, s3, s4) = (s1, s2, Regset.add (fst a) s3, Regset.add (snd a) s4) \/
        f a (s1, s2, s3, s4) = (s1, s2, Regset.add (snd a) s3, Regset.add (fst a) s4)).
unfold f.
destruct (env (snd a)); destruct (env (fst a)); unfold rr1, rr2, rr3, rr4; simpl.
left. reflexivity.
right. right. right. reflexivity.
right. right. left. reflexivity.
right. left. reflexivity.
destruct H0.
rewrite H0 in H.

generalize (IHl (SetRegReg.add a s1) s2 _ _ H).
intro H1. destruct H1.
left. assumption.
destruct H1.

destruct (proj1 (add_iff _ _ _) H1).
left. apply HH. left. intuition.
right. left. assumption.
right. right. assumption.
destruct H0.
rewrite H0 in H.
generalize (IHl s1 (SetRegReg.add a s2) _ _ H).
intro H1. destruct H1.
left. assumption.
destruct H1.
right. left. assumption.
destruct (proj1 (add_iff _ _ _) H1).
left. apply HH. left. intuition.
right. right. assumption.
destruct H0.
rewrite H0 in H.
generalize (IHl s1 s2 _ _ H).
intro H1. destruct H1.
left. assumption.
destruct H1.
right. left. assumption.
right. right. assumption.
rewrite H0 in H.
generalize (IHl s1 s2 _ _ H).
intro H1. destruct H1.
left. assumption.
destruct H1.
right. left. assumption.
right. right. assumption.
generalize (H0 _ _ _ _ _ H). clear H0. intro H0.
destruct H0.
assumption.
destruct H0; elim (SetRegReg.empty_1 H0).
Qed.

Lemma in_partition_in_snd : forall e s env,
SetRegReg.In e (rr2 (regreg_edge_type_partition s env)) ->
SetRegReg.In e s.

Proof.
intros e s env H.
unfold regreg_edge_type_partition in H.
set (f := fun (e : SetRegReg.elt) (s : regregpartition) =>
             match env (fst e) with
             | Tint =>
                 match env (snd e) with
                 | Tint =>
                     (SetRegReg.add e (rr1 s), rr2 s,
                     Regset.add (fst e) (Regset.add (snd e) (rr3 s)), 
                     rr4 s)
                 | Tfloat =>
                     (rr1 s, rr2 s, Regset.add (fst e) (rr3 s),
                     Regset.add (snd e) (rr4 s))
                 end
             | Tfloat =>
                 match env (snd e) with
                 | Tint =>
                     (rr1 s, rr2 s, Regset.add (snd e) (rr3 s),
                     Regset.add (fst e) (rr4 s))
                 | Tfloat =>
                     (rr1 s, SetRegReg.add e (rr2 s), rr3 s,
                     Regset.add (fst e) (Regset.add (snd e) (rr4 s)))
                 end
             end).
unfold regregpartition in *. fold f in H.

assert (forall e set1 set2 set3 set4, SetRegReg.In e (rr2 (SetRegReg.fold f s (set1, set2, set3, set4))) ->
                      SetRegReg.In e s \/ SetRegReg.In e set1 \/ SetRegReg.In e set2).
clear H.
intros e' s1 s2 s3 s4 H.
rewrite SetRegReg.fold_1 in H.
generalize H. generalize s1 s2 s3 s4. clear s1 s2 s3 s4 H.
generalize (SetRegReg.elements_2). intro HH.
generalize (HH s). clear HH. intro HH.
induction (SetRegReg.elements s).
simpl. right. right. assumption.
intros s1 s2 s3 s4 H.
simpl in H.
assert ((forall x : SetRegReg.elt,
       SetoidList.InA (fun x0 y : OrderedRegReg.t => fst x0 = fst y /\ snd x0 = snd y) x l ->
       SetRegReg.In x s)).
intros. apply HH. right. assumption.
generalize (IHl H0). clear IHl H0. intro IHl.
assert (f a (s1, s2, s3, s4) = (SetRegReg.add a s1, s2, Regset.add (fst a) (Regset.add (snd a) s3), s4) \/
        f a (s1, s2, s3, s4) = (s1, SetRegReg.add a s2, s3, Regset.add (fst a) (Regset.add (snd a) s4)) \/
        f a (s1, s2, s3, s4) = (s1, s2, Regset.add (fst a) s3, Regset.add (snd a) s4) \/
        f a (s1, s2, s3, s4) = (s1, s2, Regset.add (snd a) s3, Regset.add (fst a) s4)).
unfold f.
destruct (env (snd a)); destruct (env (fst a)); unfold rr1, rr2, rr3, rr4; simpl.
left. reflexivity.
right. right. right. reflexivity.
right. right. left. reflexivity.
right. left. reflexivity.
destruct H0.
rewrite H0 in H.

generalize (IHl (SetRegReg.add a s1) s2 _ _ H).
intro H1. destruct H1.
left. assumption.
destruct H1.

destruct (proj1 (add_iff _ _ _) H1).
left. apply HH. left. intuition.
right. left. assumption.
right. right. assumption.
destruct H0.
rewrite H0 in H.
generalize (IHl s1 (SetRegReg.add a s2) _ _ H).
intro H1. destruct H1.
left. assumption.
destruct H1.
right. left. assumption.
destruct (proj1 (add_iff _ _ _) H1).
left. apply HH. left. intuition.
right. right. assumption.
destruct H0.
rewrite H0 in H.
generalize (IHl s1 s2 _ _ H).
intro H1. destruct H1.
left. assumption.
destruct H1.
right. left. assumption.
right. right. assumption.
rewrite H0 in H.
generalize (IHl s1 s2 _ _ H).
intro H1. destruct H1.
left. assumption.
destruct H1.
right. left. assumption.
right. right. assumption.
generalize (H0 _ _ _ _ _ H). clear H0. intro H0.
destruct H0.
assumption.
destruct H0; elim (SetRegReg.empty_1 H0).
Qed.

Lemma in_partition_type_fst : forall e s env,
SetRegReg.In e (rr1 (regreg_edge_type_partition s env)) ->
env (fst e) = Tint /\ env (snd e) = Tint.

Proof.
intros e s env H.
unfold regreg_edge_type_partition in H.
set (f := fun (e : SetRegReg.elt) (s : regregpartition) =>
             match env (fst e) with
             | Tint =>
                 match env (snd e) with
                 | Tint =>
                     (SetRegReg.add e (rr1 s), rr2 s,
                     Regset.add (fst e) (Regset.add (snd e) (rr3 s)), 
                     rr4 s)
                 | Tfloat =>
                     (rr1 s, rr2 s, Regset.add (fst e) (rr3 s),
                     Regset.add (snd e) (rr4 s))
                 end
             | Tfloat =>
                 match env (snd e) with
                 | Tint =>
                     (rr1 s, rr2 s, Regset.add (snd e) (rr3 s),
                     Regset.add (fst e) (rr4 s))
                 | Tfloat =>
                     (rr1 s, SetRegReg.add e (rr2 s), rr3 s,
                     Regset.add (fst e) (Regset.add (snd e) (rr4 s)))
                 end
             end).
unfold regregpartition in *. fold f in H.

cut (forall e set1 set2 set3 set4, SetRegReg.In e (rr1 (SetRegReg.fold f s (set1, set2, set3, set4))) ->   
              (env (fst e) = Tint /\ env (snd e) = Tint) \/ SetRegReg.In e set1).

intros.
generalize (H0 _ _ _ _ _ H). clear H H0. intro H.
destruct H. assumption. elim (SetRegReg.empty_1 H).

(* cut property *)
intros.
generalize H0. clear H H0. intro H. 
rewrite SetRegReg.fold_1 in H.
generalize H. clear H. generalize set1 set2 set3 set4. 
induction (SetRegReg.elements s); intros s1 s2 s3 s4 H.
simpl in H. right. assumption.
simpl in H.

assert ((f a (s1, s2, s3, s4) = (SetRegReg.add a s1, s2, Regset.add (fst a) (Regset.add (snd a) s3), s4) /\ 
                         env (fst a) = Tint /\
                         env (snd a) = Tint)\/
        (f a (s1, s2, s3, s4) = (s1, SetRegReg.add a s2, s3, Regset.add (fst a) (Regset.add (snd a) s4)) /\
                         env (fst a) = Tfloat /\
                         env (snd a) = Tfloat) \/
        f a (s1, s2, s3, s4) = (s1,s2, Regset.add (fst a) s3, Regset.add (snd a) s4) \/
        f a (s1, s2, s3, s4) = (s1,s2, Regset.add (snd a) s3, Regset.add (fst a) s4)
).
unfold f.
destruct (env (snd a)); destruct (env (fst a)); unfold rr1, rr2, rr3, rr4; simpl.
left. auto.
right. right. right. reflexivity.
right. right. left. reflexivity.
right. left. auto.

destruct H0.
destruct H0. destruct H1. rewrite H0 in H.
generalize (IHl (SetRegReg.add a s1) s2 _ _ H). intro H3.
destruct H3.
left. assumption.
destruct (proj1 (add_iff _ _ _) H3).
left. intuition. rewrite <-H5. auto. rewrite <-H6. auto.
right. assumption.

destruct H0. destruct H0. destruct H1. rewrite H0 in H.
apply (IHl s1 (SetRegReg.add a s2) _ _ H).

destruct H0. rewrite H0 in H. apply (IHl s1 s2 _ _ H).
rewrite H0 in H. apply (IHl s1 s2 _ _ H).
Qed.

Lemma in_partition_type_snd : forall e s env,
SetRegReg.In e (rr2 (regreg_edge_type_partition s env)) ->
env (fst e) = Tfloat /\ env (snd e) = Tfloat.

Proof.
intros e s env H.
unfold regreg_edge_type_partition in H.
set (f := fun (e : SetRegReg.elt) (s : regregpartition) =>
             match env (fst e) with
             | Tint =>
                 match env (snd e) with
                 | Tint =>
                     (SetRegReg.add e (rr1 s), rr2 s,
                     Regset.add (fst e) (Regset.add (snd e) (rr3 s)), 
                     rr4 s)
                 | Tfloat =>
                     (rr1 s, rr2 s, Regset.add (fst e) (rr3 s),
                     Regset.add (snd e) (rr4 s))
                 end
             | Tfloat =>
                 match env (snd e) with
                 | Tint =>
                     (rr1 s, rr2 s, Regset.add (snd e) (rr3 s),
                     Regset.add (fst e) (rr4 s))
                 | Tfloat =>
                     (rr1 s, SetRegReg.add e (rr2 s), rr3 s,
                     Regset.add (fst e) (Regset.add (snd e) (rr4 s)))
                 end
             end).
unfold regregpartition in *. fold f in H.

cut (forall e set1 set2 set3 set4, SetRegReg.In e (rr2 (SetRegReg.fold f s (set1, set2, set3, set4))) ->   
              (env (fst e) = Tfloat /\ env (snd e) = Tfloat) \/ SetRegReg.In e set2).

intros.
generalize (H0 _ _ _ _ _ H). clear H H0. intro H.
destruct H. assumption. elim (SetRegReg.empty_1 H).

(* cut property *)
intros.
generalize H0. clear H H0. intro H. 
rewrite SetRegReg.fold_1 in H.
generalize H. clear H. generalize set1 set2 set3 set4. 
induction (SetRegReg.elements s); intros s1 s2 s3 s4 H.
simpl in H. right. assumption.
simpl in H.

assert ((f a (s1, s2, s3, s4) = (SetRegReg.add a s1, s2, Regset.add (fst a) (Regset.add (snd a) s3), s4) /\ 
                         env (fst a) = Tint /\
                         env (snd a) = Tint)\/
        (f a (s1, s2, s3, s4) = (s1, SetRegReg.add a s2, s3, Regset.add (fst a) (Regset.add (snd a) s4)) /\
                         env (fst a) = Tfloat /\
                         env (snd a) = Tfloat) \/
        f a (s1, s2, s3, s4) = (s1,s2, Regset.add (fst a) s3, Regset.add (snd a) s4) \/
        f a (s1, s2, s3, s4) = (s1,s2, Regset.add (snd a) s3, Regset.add (fst a) s4)
).
unfold f.
destruct (env (snd a)); destruct (env (fst a)); unfold rr1, rr2, rr3, rr4; simpl.
left. auto.
right. right. right. reflexivity.
right. right. left. reflexivity.
right. left. auto.

destruct H0.
destruct H0. rewrite H0 in H.
apply (IHl (SetRegReg.add a s1) s2 _ _ H).
destruct H0. destruct H0. rewrite H0 in H.
generalize (IHl s1 (SetRegReg.add a s2) _ _ H). intro.
destruct H2.
left. assumption.
destruct (proj1 (add_iff _ _ _) H2).
left. intuition. rewrite <-H1. auto. rewrite <-H6. auto.
right. assumption.

destruct H0. rewrite H0 in H. apply (IHl _ _ _ _ H).

rewrite H0 in H. apply (IHl s1 s2 _ _ H).
Qed.

Definition regmregpartition : Type := SetRegMreg.t*SetRegMreg.t*Regset.t*Regset.t*MRegset.t*MRegset.t.

Definition rm1 := fun (p : regmregpartition) => fst (fst (fst (fst (fst p)))).
Definition rm2 := fun (p : regmregpartition) => snd (fst (fst (fst (fst p)))).
Definition rm3 := fun (p : regmregpartition) => snd (fst (fst (fst p))).
Definition rm4 := fun (p : regmregpartition) => snd (fst (fst p)).
Definition rm5 := fun (p : regmregpartition) => snd (fst p).
Definition rm6 := fun (p : regmregpartition) => snd p.

Module Import SRMFacts := Facts SetRegMreg.

Definition regmreg_edge_type_partition s env :=
SetRegMreg.fold (fun e s => match env (fst e), mreg_type (snd e) with
  | Tint, Tint => (SetRegMreg.add e (rm1 s), rm2 s, 
                          Regset.add (fst e) (rm3 s), rm4 s,
                          MRegset.add (snd e) (rm5 s), rm6 s)
  | Tfloat, Tfloat => (rm1 s, SetRegMreg.add e (rm2 s),
                          rm3 s, Regset.add (fst e) (rm4 s),
                          rm5 s, MRegset.add (snd e) (rm6 s))
  | Tint, Tfloat => (rm1 s, rm2 s, 
                          Regset.add (fst e) (rm3 s), rm4 s,
                          rm5 s, MRegset.add (snd e) (rm6 s))
  |Tfloat, Tint => (rm1 s, rm2 s, 
                          rm3 s, Regset.add (fst e) (rm4 s),
                          MRegset.add (snd e) (rm5 s), rm6 s)
  end)
s
(SetRegMreg.empty, SetRegMreg.empty, Regset.empty, Regset.empty, MRegset.empty, MRegset.empty).

Lemma in_mreg_partition_in_fst : forall e s env,
SetRegMreg.In e (rm1 (regmreg_edge_type_partition s env)) ->
SetRegMreg.In e s.

Proof.
Admitted.
(*
intros e s env H.
unfold regmreg_edge_type_partition in H.
set (f := (fun (e : SetRegMreg.elt) (s : SetRegMreg.t * SetRegMreg.t) =>
             match env (fst e) with
             | Tint =>
                 match mreg_type (snd e) with
                 | Tint => (SetRegMreg.add e (fst s), snd s)
                 | Tfloat => s
                 end
             | Tfloat =>
                 match mreg_type (snd e) with
                 | Tint => s
                 | Tfloat => (fst s, SetRegMreg.add e (snd s))
                 end
             end)) in H.

assert (forall e set1 set2, SetRegMreg.In e (fst (SetRegMreg.fold f s (set1, set2))) ->
                         SetRegMreg.In e s \/ SetRegMreg.In e set1 \/ SetRegMreg.In e set2).
clear H.
intros e' s1 s2 H.
rewrite SetRegMreg.fold_1 in H.
generalize H. generalize s1 s2. clear s1 s2 H.
generalize (SetRegMreg.elements_2). intro HH.
generalize (HH s). clear HH. intro HH.
induction (SetRegMreg.elements s).
simpl. right. left. assumption.
intros s1 s2 H.
simpl in H.
assert ((forall x : SetRegMreg.elt,
       SetoidList.InA (fun x0 y : OrderedRegMreg.t => fst x0 = fst y /\ snd x0 = snd y) x l ->
       SetRegMreg.In x s)).
intros. apply HH. right. assumption.
generalize (IHl H0). clear IHl H0. intro IHl.
assert (f a (s1, s2) = (SetRegMreg.add a s1, s2) \/
        f a (s1, s2) = (s1, SetRegMreg.add a s2) \/
        f a (s1, s2) = (s1,s2)).
unfold f.
destruct (mreg_type (snd a)); destruct (env (fst a)); simpl.
left. reflexivity.
right. right. reflexivity.
right. right. reflexivity.
right. left. reflexivity.
destruct H0.
rewrite H0 in H.

generalize (IHl (SetRegMreg.add a s1) s2 H).
intro H1. destruct H1.
left. assumption.
destruct H1.

destruct (proj1 (add_iff _ _ _) H1).
left. apply HH. left. intuition.
right. left. assumption.
right. right. assumption.
destruct H0.
rewrite H0 in H.
generalize (IHl s1 (SetRegMreg.add a s2) H).
intro H1. destruct H1.
left. assumption.
destruct H1.
right. left. assumption.
destruct (proj1 (add_iff _ _ _) H1).
left. apply HH. left. intuition.
right. right. assumption.
rewrite H0 in H.
generalize (IHl s1 s2 H).
intro H1. destruct H1.
left. assumption.
destruct H1.
right. left. assumption.
right. right. assumption.
generalize (H0 _ _ _ H). clear H0. intro H0.
destruct H0.
assumption.
destruct H0; elim (SetRegMreg.empty_1 H0).
Qed.
*)

Lemma in_mreg_partition_in_snd : forall e s env,
SetRegMreg.In e (rm2 (regmreg_edge_type_partition s env)) ->
SetRegMreg.In e s.

Proof.
Admitted.
(*
intros e s env H.
unfold regmreg_edge_type_partition in H.
set (f := (fun (e : SetRegMreg.elt) (s : SetRegMreg.t * SetRegMreg.t) =>
             match env (fst e) with
             | Tint =>
                 match mreg_type (snd e) with
                 | Tint => (SetRegMreg.add e (fst s), snd s)
                 | Tfloat => s
                 end
             | Tfloat =>
                 match mreg_type (snd e) with
                 | Tint => s
                 | Tfloat => (fst s, SetRegMreg.add e (snd s))
                 end
             end)) in H.

assert (forall e set1 set2, SetRegMreg.In e (snd (SetRegMreg.fold f s (set1, set2))) ->
                      SetRegMreg.In e s \/ SetRegMreg.In e set1 \/ SetRegMreg.In e set2).
clear H.
intros e' s1 s2 H.
rewrite SetRegMreg.fold_1 in H.
generalize H. generalize s1 s2. clear s1 s2 H.
generalize (SetRegMreg.elements_2). intro HH.
generalize (HH s). clear HH. intro HH.
induction (SetRegMreg.elements s).
simpl. right. right. assumption.
intros s1 s2 H.
simpl in H.
assert ((forall x : SetRegMreg.elt,
       SetoidList.InA (fun x0 y : OrderedRegMreg.t => fst x0 = fst y /\ snd x0 = snd y) x l ->
       SetRegMreg.In x s)).
intros. apply HH. right. assumption.
generalize (IHl H0). clear IHl H0. intro IHl.
assert (f a (s1, s2) = (SetRegMreg.add a s1, s2) \/
        f a (s1, s2) = (s1, SetRegMreg.add a s2) \/
        f a (s1, s2) = (s1,s2)).
unfold f.
destruct (mreg_type (snd a)); destruct (env (fst a)); simpl.
left. reflexivity.
right. right. reflexivity.
right. right. reflexivity.
right. left. reflexivity.
destruct H0.
rewrite H0 in H.

generalize (IHl (SetRegMreg.add a s1) s2 H).
intro H1. destruct H1.
left. assumption.
destruct H1.

destruct (proj1 (add_iff _ _ _) H1).
left. apply HH. left. intuition.
right. left. assumption.
right. right. assumption.
destruct H0.
rewrite H0 in H.
generalize (IHl s1 (SetRegMreg.add a s2) H).
intro H1. destruct H1.
left. assumption.
destruct H1.
right. left. assumption.
destruct (proj1 (add_iff _ _ _) H1).
left. apply HH. left. intuition.
right. right. assumption.
rewrite H0 in H.
generalize (IHl s1 s2 H).
intro H1. destruct H1.
left. assumption.
destruct H1.
right. left. assumption.
right. right. assumption.
generalize (H0 _ _ _ H). clear H0. intro H0.
destruct H0.
assumption.
destruct H0; elim (SetRegMreg.empty_1 H0).
Qed.
*)

Lemma in_mreg_partition_type_fst : forall e s env,
SetRegMreg.In e (rm1 (regmreg_edge_type_partition s env)) ->
env (fst e) = Tint /\ mreg_type (snd e) = Tint.

Proof.
Admitted.
(*
intros e s env H.
unfold regmreg_edge_type_partition in H.
set (f := (fun (e : SetRegMreg.elt) (s : SetRegMreg.t * SetRegMreg.t) =>
             match env (fst e) with
             | Tint =>
                 match mreg_type (snd e) with
                 | Tint => (SetRegMreg.add e (fst s), snd s)
                 | Tfloat => s
                 end
             | Tfloat =>
                 match mreg_type (snd e) with
                 | Tint => s
                 | Tfloat => (fst s, SetRegMreg.add e (snd s))
                 end
             end)) in H.

cut (forall e set1 set2, SetRegMreg.In e (fst (SetRegMreg.fold f s (set1, set2))) ->   
              (env (fst e) = Tint /\ mreg_type (snd e) = Tint) \/ SetRegMreg.In e set1).

intros.
generalize (H0 _ _ _ H). clear H H0. intro H.
destruct H. assumption. elim (SetRegMreg.empty_1 H).

(* cut property *)
intros.
generalize H0. clear H H0. intro H. 
rewrite SetRegMreg.fold_1 in H.
generalize H. clear H. generalize set1 set2. 
induction (SetRegMreg.elements s); intros s1 s2 H.
simpl in H. right. assumption.
simpl in H.

assert ((f a (s1, s2) = (SetRegMreg.add a s1, s2) /\ 
                         env (fst a) = Tint /\
                         mreg_type (snd a) = Tint)\/
        (f a (s1, s2) = (s1, SetRegMreg.add a s2) /\
                         env (fst a) = Tfloat /\
                         mreg_type (snd a) = Tfloat) \/
        f a (s1, s2) = (s1,s2)).
unfold f.
destruct (mreg_type (snd a)); destruct (env (fst a)); simpl.
left. auto.
right. right. reflexivity.
right. right. reflexivity.
right. left. auto.

destruct H0.
destruct H0. destruct H1. rewrite H0 in H.
generalize (IHl (SetRegMreg.add a s1) s2 H). intro H3.
destruct H3.
left. assumption.
destruct (proj1 (add_iff _ _ _) H3).
left. intuition. rewrite <-H5. auto. rewrite <-H6. auto.
right. assumption.

destruct H0. destruct H0. destruct H1. rewrite H0 in H.
apply (IHl s1 (SetRegMreg.add a s2) H).

rewrite H0 in H.
apply (IHl s1 s2 H).
Qed.
*)

Lemma in_mreg_partition_type_snd : forall e s env,
SetRegMreg.In e (rm2 (regmreg_edge_type_partition s env)) ->
env (fst e) = Tfloat /\ mreg_type (snd e) = Tfloat.

Proof.
Admitted.
(*
intros e s env H.
unfold regmreg_edge_type_partition in H.
set (f := (fun (e : SetRegMreg.elt) (s : SetRegMreg.t * SetRegMreg.t) =>
             match env (fst e) with
             | Tint =>
                 match mreg_type (snd e) with
                 | Tint => (SetRegMreg.add e (fst s), snd s)
                 | Tfloat => s
                 end
             | Tfloat =>
                 match mreg_type (snd e) with
                 | Tint => s
                 | Tfloat => (fst s, SetRegMreg.add e (snd s))
                 end
             end)) in H.

cut (forall e set1 set2, SetRegMreg.In e (snd (SetRegMreg.fold f s (set1, set2))) ->   
              (env (fst e) = Tfloat /\ mreg_type (snd e) = Tfloat) \/ SetRegMreg.In e set2).

intros.
generalize (H0 _ _ _ H). clear H H0. intro H.
destruct H. assumption. elim (SetRegMreg.empty_1 H).

(* cut property *)
intros.
generalize H0. clear H H0. intro H. 
rewrite SetRegMreg.fold_1 in H.
generalize H. clear H. generalize set1 set2. 
induction (SetRegMreg.elements s); intros s1 s2 H.
simpl in H. right. assumption.
simpl in H.

assert ((f a (s1, s2) = (SetRegMreg.add a s1, s2) /\ 
                         env (fst a) = Tint /\
                         mreg_type (snd a) = Tint)\/
        (f a (s1, s2) = (s1, SetRegMreg.add a s2) /\
                         env (fst a) = Tfloat /\
                         mreg_type (snd a) = Tfloat) \/
        f a (s1, s2) = (s1,s2)).
unfold f.
destruct (mreg_type (snd a)); destruct (env (fst a)); simpl.
left. auto.
right. right. reflexivity.
right. right. reflexivity.
right. left. auto.

destruct H0.
destruct H0. destruct H1. rewrite H0 in H.
apply (IHl (SetRegMreg.add a s1) s2 H).

destruct H0. destruct H0. destruct H1. rewrite H0 in H.
generalize (IHl s1 (SetRegMreg.add a s2) H). intro.
destruct H3.
left. auto.
destruct (proj1 (add_iff _ _ _) H3).
destruct H4. left. rewrite H4 in *. rewrite H5 in *. intuition.
right. auto.
rewrite H0 in H. apply (IHl s1 s2 H).
Qed.

Definition Typed_interfgraphs g env  :=
let (int_regreg_interf, float_regreg_interf) := 
    regreg_edge_type_partition (interf_reg_reg g) env in
let (int_regmreg_interf, float_regmreg_interf) := 
    regmreg_edge_type_partition (interf_reg_mreg g) env in
let (int_regreg_pref, float_regreg_pref) :=
    regreg_edge_type_partition (pref_reg_reg g) env in
let (int_regmreg_pref, float_regmreg_pref) :=
    regmreg_edge_type_partition (pref_reg_mreg g) env in
(mkgraph int_regreg_interf   int_regmreg_interf   int_regreg_pref   int_regmreg_pref,
 mkgraph float_regreg_interf float_regmreg_interf float_regreg_pref float_regmreg_pref).
*)



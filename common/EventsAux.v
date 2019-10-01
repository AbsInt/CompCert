
Require Import String.
Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.


Lemma Forall2_impl:
  forall {A B} (r1 r2:A-> B -> Prop) l1 l2, (forall a b, r1 a b -> r2 a b) ->
          Forall2 r1 l1 l2 -> Forall2 r2 l1 l2.
Proof.
  intros until l1; induction l1.
  - intros * ? H; inv H; constructor.
  - intros * ? H; inv H; constructor; eauto.
Qed.

(* New strong injection. This relation is injective! *)
Inductive inject_strong (mi : meminj) : val -> val -> Prop :=
    inject_int : forall i : int, inject_strong mi (Vint i) (Vint i)
  | inject_long : forall i : int64, inject_strong mi (Vlong i) (Vlong i)
  | inject_float : forall f : float, inject_strong mi (Vfloat f) (Vfloat f)
  | inject_single : forall f : float32, inject_strong mi (Vsingle f) (Vsingle f)
  | inject_ptr : forall (b1 : block) (ofs1 : ptrofs) (b2 : block) (ofs2 : ptrofs) (delta : Z),
                 mi b1 = Some (b2, delta) ->
                 ofs2 = Ptrofs.add ofs1 (Ptrofs.repr delta) ->
                 inject_strong mi (Vptr b1 ofs1) (Vptr b2 ofs2)
  | val_inject_undef : inject_strong mi Vundef Vundef.
Inductive memval_inject_strong (f : meminj) : memval -> memval -> Prop :=
    memval_inject_byte_str : forall n : byte, memval_inject_strong f (Byte n) (Byte n)
  | memval_inject_frag_str : forall (v1 v2 : val) (q : quantity) (n : nat),
                         inject_strong f v1 v2 ->
                         memval_inject_strong f (Fragment v1 q n) (Fragment v2 q n)
  | memval_inject_undef_str : memval_inject_strong f Undef Undef.
                                              
Definition list_memval_inject mu:= Forall2 (memval_inject mu).
Definition list_memval_inject_strong mu:= Forall2 (memval_inject_strong mu).
Lemma memval_inject_strong_weak:
         forall f v1 v2, memval_inject_strong f v1 v2 ->  memval_inject f v1 v2.
Proof. intros * HH; inv HH; econstructor; auto. inv H; econstructor; eauto. Qed.
Lemma list_memval_inject_strong_weak:
  forall f vals1 vals2, list_memval_inject_strong f vals1 vals2 ->
                   list_memval_inject f vals1 vals2.
Proof. intros *; eapply Forall2_impl; apply memval_inject_strong_weak. Qed.

(*Injection for block ranges*)
Inductive inject_hi_low (mu:meminj): (block * Z * Z) -> (block * Z * Z) -> Prop:=
| HiLow: forall b1 b2 hi low delt,
    mu b1 = Some(b2, delt) ->
    inject_hi_low mu (b1, hi, low) (b2, hi+delt, low+delt).
Definition list_inject_hi_low mu := Forall2 (inject_hi_low mu).
  
(*
  Delta Permission Maps:
  A change in memory permissions.
  - They have the same shape as the memories
  - they return [None], if the permission doesn't change at that location
  - return [Some perm], if the new permission is [perm].
*)
Notation delta_perm_map := (Maps.PTree.t (Z -> option (option permission))).
Definition inject_Z_map {A} (delt: Z) (f1 f2: (Z -> option A)): Prop:=
  forall ofs p, f1 ofs = Some p -> f1 ofs = f2 (ofs+ delt).
    
Record inject_delta_map (mu: meminj)(dpm1 dpm2: delta_perm_map): Prop:=
  { DPM_image: (*All permissions changed are mapped*)
      forall b1 f1, (Maps.PTree.get b1 dpm1) = Some f1 ->
      exists b2 delt f2, mu b1 = Some (b2, delt) /\
                     Maps.PTree.get b2 dpm2 = Some f2 /\
            inject_Z_map delt f1 f2
    ;DPM_preimage:
       forall b2 ofs2 f2 p,
         Maps.PTree.get b2 dpm2 = Some f2 ->
         f2 ofs2 = p ->
         exists b1 f1 ofs1 delt,
           mu b1 = Some(b2, delt) /\
           Maps.PTree.get b1 dpm1 = Some f1 /\
           f1 ofs1 = p /\
           ofs2 = ofs1 + delt
  }.








(** *Relations that are monotonic w.r.t. injections*)
Definition inj_monotone{A} (R:meminj -> A -> A-> Prop):Prop:=
  forall (a b:A) f f',  R f a b -> inject_incr f f' -> R f' a b.
Lemma Forall2_incr:
  forall {A} (R: meminj -> A -> A -> Prop),
    inj_monotone R ->
    inj_monotone (fun j => Forall2 (R j)).
Proof.
  intros A R HR; unfold inj_monotone.
  induction a; intros ? ? ? HH; inv HH; intros; constructor; eauto.
Qed.
Create HintDb inj_mono. Hint Resolve Forall2_incr: inj_mono.
Ltac inj_mono_tac:=
  match goal with
    [|- inj_monotone ?R ] =>
    (* If it's a list try the list lemma *)
    try (eapply Forall2_incr; eauto with  inj_mono);
    intros ???? ?HR ?Hincr; inv HR;
    try solve[econstructor; eauto with inj_mono]
  | _ => fail "Expected goal: inj_monotone ?R" 
  end.








(** * Relations that compose with injections *)
Definition composes_inj {A} (R: meminj -> A -> A ->Prop):=
  forall j12 j23 x1 x2 x3, R j12 x1 x2 -> R j23 x2 x3 -> R (compose_meminj j12 j23) x1 x3.
Create HintDb compose_inj.
Lemma Forall2_compose:
  forall {A} (R: meminj -> A -> A -> Prop),
    composes_inj R -> composes_inj (fun j => Forall2 (R j)).
Proof.
  intros ** ?? ls. induction ls; intros * H0 H1;
  inv H0; inv H1; constructor; eauto.
Qed.
Hint Resolve Forall2_compose: compose_inj.
Ltac composition_arithmetic:=
  (* Solves the Ptrofs.add... goal that results from 
       injecting a pointer twice: the offsets are added 
       in two different ways *)
  rewrite Ptrofs.add_assoc; decEq;
  unfold Ptrofs.add; apply Ptrofs.eqm_samerepr; auto with ints.
Ltac composed_injections_injection_case j12 j23:=
  match goal with
  |[ H12: j12 _ = Some _, H23: j23 _ = Some _ |-
     context[compose_meminj j12 j23] ] =>
   econstructor;
   try (unfold compose_meminj; rewrite H12; rewrite H23); eauto;
   try composition_arithmetic; eauto with compose_inj
  end.
Ltac composed_injections:=
  match goal with
  |[|- composes_inj ?R] =>
   let H1:= fresh "H1" in let H2:= fresh "H2" in 
                          intros j12 j23  ??? H1 H2;
                          inv H1; auto; inv H2; auto;
                          try solve[econstructor; eauto with compose_inj];
                          try composed_injections_injection_case j12 j23
  | _ => fail "Not the shape expected"
  end.
Ltac rewrite_compose_meminj:=
  match goal with
  |[ H12: ?j12 _ = Some _, H23: ?j23 _ = Some _ |-
     context[compose_meminj ?j12 ?j23]
   ] => unfold compose_meminj; rewrite H12, H23
  end.


  Lemma inject_delta_map_compose: composes_inj inject_delta_map.
Proof. intros ? **.
       inv H; inv H0.
       constructor.
       - intros; exploit  DPM_image0; eauto.
         intros (?&?&?&?&?&?).
         exploit  DPM_image1; eauto.
         intros (?&?&?&?&?&?).
         repeat (econstructor; eauto).
         unfold compose_meminj;
           rewrite H0, H3; reflexivity.
         intros ** ofs. 
         intros ??HH.
         erewrite H2; eauto.
         erewrite H5; eauto. f_equal. omega.
         rewrite <- HH. exploit H2; eauto.
       - intros; exploit  DPM_preimage1; eauto.
         intros (?&?&?&?&?&?&?&?).
         exploit  DPM_preimage0; eauto.
         intros (?&?&?&?&?&?&?&?).
         repeat (econstructor; eauto).
         unfold compose_meminj; rewrite H5, H1; reflexivity.
         subst; eauto; omega.
Qed.
Hint Resolve inject_delta_map_compose: compose_inj.

Lemma inject_hi_low_compose: composes_inj inject_hi_low.
Proof. composed_injections; do 2 rewrite Zplus_assoc_reverse.
       econstructor; rewrite_compose_meminj; reflexivity. Qed.
Hint Resolve inject_hi_low_compose:compose_inj. 
Lemma list_inject_hi_low_compose: composes_inj list_inject_hi_low.
Proof. eauto with compose_inj. Qed.
Hint Resolve list_inject_hi_low_compose:compose_inj. 



(** *Strong interpolation:
    An injection relation, induced by a composed meminj,
    can be split into a strong one and a regular one.
*)
  Definition strong_interpolation {A} (R: meminj -> A -> A -> Prop)
             (R_strong: meminj -> A -> A -> Prop):=
    forall v1 v3 j12 j23, R (compose_meminj j12 j23) v1 v3 ->
      exists v2,  R_strong j12 v1 v2 /\ R j23 v2 v3.
  Create HintDb str_interp.
  Ltac case_compose_meminj:=
    match goal with
    | [ H: compose_meminj ?f1 ?f2 ?b = Some _  |- _ ] =>
      unfold compose_meminj in H; repeat match_case in H;
      subst;
      try match goal with
          | [ H: Some _ = Some _ |- _ ] => inv H
          end
    end.
  (* apply a strong interpolation lemma in a hypothesis*)
  Lemma list_str_interpol:
    forall {A} (R R_str: meminj -> A -> A -> Prop) ,
      strong_interpolation R R_str ->
      strong_interpolation (fun f => Forall2 (R f))
                           (fun f => Forall2 (R_str f)).
Proof.
  intros.
  unfold strong_interpolation.
  induction v1; intros.
  - inv H0; do 3 econstructor. 
  - inv H0.
    exploit IHv1; eauto. intros (?&?&?).
    exploit H; eauto. intros (?&?&?).
    do 3 econstructor; eauto.
Qed.
Lemma str_interpol_cut:
  forall A R R_str,
    @strong_interpolation A R R_str -> 
    @strong_interpolation A R R_str.
Proof. eauto. Qed.
Ltac use_interpolations_in_hyps:=
  match goal with
  | [ H: ?R (compose_meminj ?j12 ?j23) _ _ |- _ ] =>
    eapply (@str_interpol_cut _ R) in H;
    [ destruct H as (?&?&?) | solve[eauto with str_interp]]
  end.
Ltac str_interp:=
  match goal with
    [|- strong_interpolation ?R ?R_Str] =>
    (* try if it's a list*)
    try (eapply list_str_interpol;
         eauto with str_interp);
    intros ???? ?HR; inv HR;
    try case_compose_meminj;
    (* exploit one interpolation from the hypothesis *)
    repeat use_interpolations_in_hyps;
    (*try easy cases *)
    try solve[ do 3 econstructor];
    try solve[repeat (econstructor; eauto with str_interp)]
  end.

Lemma inject_delta_interpolation: strong_interpolation inject_delta_map inject_delta_map.
Proof.
  str_interp.
  remember (Maps.PTree.elements v1) as ls1.
  set (mapped_delta:= fun {A} (j:meminj) (ls: list (positive * (Z -> A))) =>
                        @fold_left (Maps.PTree.t _) (positive * _)
                          (fun dmap b1_f1 =>
                             let (b1, f):= b1_f1 in
                             match j b1  with
                             | Some (b2, delt) =>
                               Maps.PTree.set
                                 b1 (fun ofs => f (ofs - delt)) dmap
                             | _ => dmap
                                     end)
                          ls (Maps.PTree.empty (Z -> A))).
       exists (mapped_delta _ j12 ls1); split.
       - econstructor; intros.
         + exploit DPM_image0; try eassumption;
             intros (?&?&?&?&?&?).
           case_compose_meminj.
           repeat (econstructor; eauto).
           
           

Admitted.
Hint Resolve inject_delta_interpolation: str_interp.



(** *Determinism in relations *)
Definition deterministic {A B} (R: A -> B -> Prop):=
    forall a b b', R a b -> R a b' -> b = b'.
  Lemma determ_cut:
    forall A B R, @deterministic A B R -> deterministic R. Proof. eauto. Qed.
  Lemma  Forall2_determ:
    forall {A B} (R: A -> B -> Prop),
      deterministic R ->
      deterministic (Forall2 R).
  Proof.
    unfold deterministic;
      intros. revert b' H1.
    induction H0; intros.
    - inv H1; auto.
    - inv H2; f_equal.
      + eapply H; eassumption.
      + eapply IHForall2; assumption.
  Qed.
  Create HintDb determ. Hint Resolve Forall2_determ: determ.
  
    Ltac different_results:=
      match goal with
        [H: ?a = _, H0: ?a = _ |- _]=>
        rewrite H in H0; inv H0
      end.
    Ltac determ_hyp:=
      match goal with
        [H: ?R ?a ?b, H0: ?R ?a ?b' |- _] =>
        replace b with b' in * by (eapply determ_cut; eauto with determ);
        auto; clear H0
      end.
    Ltac solve_determ:=
      match goal with
        [|- forall j,  deterministic ?R ] =>
        let H:= fresh in let H0:=fresh in
        eauto with determ;
        intros ?? * H H0; inv H; inv H0;
        repeat different_results;
        repeat determ_hyp;
        eauto
      end.
    Lemma inject_delta_map_determ:
    forall (f12 : meminj), deterministic (inject_delta_map f12).  
  Proof. solve_determ.
  Admitted.
  Hint Resolve inject_delta_map_determ: determ.



  (** *Some trivial hints added to the database. *)
  Hint Immediate inject_incr_refl.
  
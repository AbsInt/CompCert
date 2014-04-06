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

(** Type-checking Linear code. *)

Require Import FSets.
Require FSetAVL.
Require Import Coqlib.
Require Import Ordered.
Require Import Maps.
Require Import Iteration.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Op.
Require Import Machregs.
Require Import Locations.
Require Import Conventions.
Require Import LTL.
Require Import Linear.

(** The typechecker for Linear enforce several properties useful for
  the proof of the [Stacking] pass:
- for each instruction, the type of the result register or slot
  agrees with the type of values produced by the instruction;
- correctness conditions on the offsets of stack slots
  accessed through [Lgetstack] and [Lsetstack] Linear instructions.
*)

(** * Tracking the flow of single-precision floats *)

Module Locset := FSetAVL.Make(OrderedLoc).

(** At each program point, we infer a set of locations that are
  guaranteed to contain single-precision floats.  [None] means
  that the program point is not reachable. *)

Definition singlefloats := option Locset.t.

Definition FSbot : singlefloats := None.
Definition FStop : singlefloats := Some Locset.empty.

Definition setreg (fs: singlefloats) (r: mreg) (t: typ) :=
  match fs with
  | None => None
  | Some s =>
      Some(if typ_eq t Tsingle then Locset.add (R r) s else Locset.remove (R r) s)
  end.

Fixpoint setregs (fs: singlefloats) (rl: list mreg) (tl: list typ) :=
  match rl, tl with
  | nil, nil => fs
  | r1 :: rs, t1 :: ts => setregs (setreg fs r1 t1) rs ts
  | _, _ => fs
  end.

Definition copyloc (fs: singlefloats) (dst src: loc) :=
  match fs with
  | None => None
  | Some s =>
      Some(if Locset.mem src s then Locset.add dst s else Locset.remove dst s)
  end.

Definition destroyed_at_call_regs :=
  List.fold_right (fun r fs => Locset.add (R r) fs) Locset.empty destroyed_at_call.

Definition callregs (fs: singlefloats) :=
  match fs with
  | None => None
  | Some s => Some (Locset.diff s destroyed_at_call_regs)
  end.

(** The forward dataflow analysis below records [singlefloats] sets
  at every label.  Sets at other program points are recomputed when
  needed. *)

Definition labelmap := PTree.t Locset.t.

(** [update_label lbl fs lm] updates the label map [lm] to reflect the
  fact that the [singlefloats] set [fs] can flow into label [lbl].
  It returns the set after the label, an updated label map, and a
  boolean indicating whether the label map changed. *)

Definition update_label (lbl: label) (fs: singlefloats) (lm: labelmap) : 
                                              singlefloats * labelmap * bool :=
  match fs, PTree.get lbl lm with
  | None, None => (None, lm, false)
  | None, Some s => (Some s, lm, false)
  | Some s, None => (Some s, PTree.set lbl s lm, true)
  | Some s1, Some s2 =>
      if Locset.subset s2 s1
      then (Some s2, lm, false)
      else let s := Locset.inter s1 s2 in (Some s, PTree.set lbl s lm, true)
  end.

(** [update_labels] is similar, for a list of labels (coming from a 
    [Ljumptable] instruction). *)

Fixpoint update_labels (lbls: list label) (fs: singlefloats) (lm: labelmap): labelmap * bool :=
  match lbls with
  | nil => (lm, false)
  | lbl1 :: lbls =>
      let '(_, lm1, changed1) := update_label lbl1 fs lm in
      let '(lm2, changed2) := update_labels lbls fs lm1 in
      (lm2, changed1 || changed2)
  end.

(** One pass of forward analysis over the code [c].  Returns an updated
  label map and a boolean indicating whether the label map changed. *)

Fixpoint ana_code (lm: labelmap) (ch: bool) (fs: singlefloats) (c: code) : labelmap * bool :=
  match c with
  | nil => (lm, ch)
  | Lgetstack sl ofs ty rd :: c =>
      ana_code lm ch (copyloc fs (R rd) (S sl ofs ty)) c
  | Lsetstack rs sl ofs ty :: c =>
      ana_code lm ch (copyloc fs (S sl ofs ty) (R rs)) c
  | Lop op args dst :: c =>
      match is_move_operation op args with
      | Some src => ana_code lm ch (copyloc fs (R dst) (R src)) c
      | None     => ana_code lm ch (setreg fs dst (snd (type_of_operation op))) c
      end
  | Lload chunk addr args dst :: c =>
      ana_code lm ch (setreg fs dst (type_of_chunk chunk)) c
  | Lstore chunk addr args src :: c =>
      ana_code lm ch fs c
  | Lcall sg ros :: c =>
      ana_code lm ch (callregs fs) c
  | Ltailcall sg ros :: c =>
      ana_code lm ch None c
  | Lbuiltin ef args res :: c =>
      ana_code lm ch (setregs fs res (proj_sig_res' (ef_sig ef))) c
  | Lannot ef args :: c =>
      ana_code lm ch fs c
  | Llabel lbl :: c =>
      let '(fs1, lm1, ch1) := update_label lbl fs lm in
      ana_code lm1 (ch || ch1) fs1 c
  | Lgoto lbl :: c =>
      let '(_, lm1, ch1) := update_label lbl fs lm in
      ana_code lm1 (ch || ch1) None c
  | Lcond cond args lbl :: c =>
      let '(_, lm1, ch1) := update_label lbl fs lm in
      ana_code lm1 (ch || ch1) fs c
  | Ljumptable r lbls :: c =>
      let '(lm1, ch1) := update_labels lbls fs lm in
      ana_code lm1 (ch || ch1) None c
  | Lreturn :: c =>
      ana_code lm ch None c
  end.

(** Iterating [ana_code] until the label map is stable. *)

Definition ana_iter (c: code) (lm: labelmap) : labelmap + labelmap :=
  let '(lm1, ch) := ana_code lm false FStop c in
  if ch then inr _ lm1 else inl _ lm.

Definition ana_function (f: function): option labelmap :=
  PrimIter.iterate _ _ (ana_iter f.(fn_code)) (PTree.empty _).

(** * The type-checker *)

(** The typing rules are presented as boolean-valued functions so that we
  get an executable type-checker for free. *)

Section WT_INSTR.

Variable funct: function.

Variable lm: labelmap.

Definition FSmem (l: loc) (fs: singlefloats) : bool :=
  match fs with None => true | Some s => Locset.mem l s end.

Definition loc_type (fs: singlefloats) (l: loc) :=
  let ty := Loc.type l in
  if typ_eq ty Tfloat && FSmem l fs then Tsingle else ty.

Definition slot_valid (sl: slot) (ofs: Z) (ty: typ): bool :=
  match sl with
  | Local => zle 0 ofs
  | Outgoing => zle 0 ofs
  | Incoming => In_dec Loc.eq (S Incoming ofs ty) (loc_parameters funct.(fn_sig))
  end &&
  match ty with
  | Tint | Tfloat | Tsingle => true
  | Tlong => false
  end.

Definition slot_writable (sl: slot) : bool :=
  match sl with
  | Local => true
  | Outgoing => true
  | Incoming => false
  end.

Definition loc_valid (l: loc) : bool :=
  match l with
  | R r => true
  | S Local ofs ty => slot_valid Local ofs ty
  | S _ _ _ => false
  end.

Fixpoint wt_code (fs: singlefloats) (c: code) : bool :=
  match c with
  | nil => true
  | Lgetstack sl ofs ty rd :: c =>
      subtype ty (mreg_type rd) &&
      slot_valid sl ofs ty &&
      wt_code (copyloc fs (R rd) (S sl ofs ty)) c
  | Lsetstack rs sl ofs ty :: c =>
      subtype (loc_type fs (R rs)) ty &&
      slot_valid sl ofs ty && slot_writable sl &&
      wt_code (copyloc fs (S sl ofs ty) (R rs)) c
  | Lop op args dst :: c =>
      match is_move_operation op args with
      | Some src =>
          typ_eq (mreg_type src) (mreg_type dst) &&
          wt_code (copyloc fs (R dst) (R src)) c
      | None =>
          let (ty_args, ty_res) := type_of_operation op in
          subtype ty_res (mreg_type dst) &&
          wt_code (setreg fs dst ty_res) c
      end
  | Lload chunk addr args dst :: c =>
      subtype (type_of_chunk chunk) (mreg_type dst) &&
      wt_code (setreg fs dst (type_of_chunk chunk)) c
  | Lstore chunk addr args src :: c =>
      wt_code fs c
  | Lcall sg ros :: c =>
      wt_code (callregs fs) c
  | Ltailcall sg ros :: c =>
      zeq (size_arguments sg) 0 &&
      wt_code None c
  | Lbuiltin ef args res :: c =>
      let ty_res := proj_sig_res' (ef_sig ef) in
      subtype_list ty_res (map mreg_type res) &&
      wt_code (setregs fs res ty_res) c
  | Lannot ef args :: c =>
      forallb loc_valid args &&
      wt_code fs c
  | Llabel lbl :: c =>
      wt_code lm!lbl c
  | Lgoto lbl :: c =>
      wt_code None c
  | Lcond cond args lbl :: c =>
      wt_code fs c
  | Ljumptable r lbls :: c =>
      wt_code None c
  | Lreturn :: c =>
      wt_code None c
  end.

End WT_INSTR.

Definition wt_funcode (f: function) (lm: labelmap) : bool :=
  wt_code f lm FStop f.(fn_code).

Definition wt_function (f: function) : bool :=
  match ana_function f with
  | None => false
  | Some lm => wt_funcode f lm
  end.

(** * Properties of the static analysis *)

Inductive FSincl: singlefloats -> singlefloats -> Prop :=
  | FSincl_none: forall fs,
      FSincl None fs
  | FSincl_subset: forall s1 s2,
      Locset.Subset s2 s1 -> FSincl (Some s1) (Some s2).

Lemma update_label_false:
  forall lbl fs lm fs' lm',
  update_label lbl fs lm = (fs', lm', false) ->
  FSincl fs lm!lbl /\ fs' = lm!lbl /\ lm' = lm.
Proof.
  unfold update_label; intros. 
  destruct fs as [s1|]; destruct lm!lbl as [s2|].
- destruct (Locset.subset s2 s1) eqn:S; inv H.
  intuition. constructor. apply Locset.subset_2; auto.
- inv H.
- inv H. intuition. constructor. 
- inv H. intuition. constructor.
Qed.

Lemma update_labels_false:
  forall fs lbls lm lm',
  update_labels lbls fs lm = (lm', false) ->
  (forall lbl, In lbl lbls -> FSincl fs lm!lbl) /\ lm' = lm.
Proof.
  induction lbls; simpl; intros. 
- inv H. tauto. 
- destruct (update_label a fs lm) as [[fs1 lm1] changed1] eqn:UL.
  destruct (update_labels lbls fs lm1) as [lm2 changed2] eqn:ULS.
  inv H. apply orb_false_iff in H2. destruct H2; subst.
  exploit update_label_false; eauto. intros (A & B & C).
  exploit IHlbls; eauto. intros (D & E). subst.
  split. intros. destruct H. congruence. auto.
  auto.
Qed.

Lemma ana_code_false:
  forall lm' c lm ch fs, ana_code lm ch fs c = (lm', false) -> ch = false /\ lm' = lm.
Proof.
  induction c; simpl; intros.
- inv H; auto. 
- destruct a; try (eapply IHc; eauto; fail).
  + destruct (is_move_operation o l); eapply IHc; eauto.
  + destruct (update_label l fs lm) as [[fs1 lm1] ch1] eqn:UL.
    exploit IHc; eauto. intros [A B]. apply orb_false_iff in A; destruct A; subst.
    exploit update_label_false; eauto. intros (C & D & E).
    auto.
  + destruct (update_label l fs lm) as [[fs1 lm1] ch1] eqn:UL.
    exploit IHc; eauto. intros [A B]. apply orb_false_iff in A; destruct A; subst.
    exploit update_label_false; eauto. intros (C & D & E). 
    auto.
  + destruct (update_label l0 fs lm) as [[fs1 lm1] ch1] eqn:UL.
    exploit IHc; eauto. intros [A B]. apply orb_false_iff in A; destruct A; subst.
    exploit update_label_false; eauto. intros (C & D & E). 
    auto.
  + destruct (update_labels l fs lm) as [lm1 ch1] eqn:UL.
    exploit IHc; eauto. intros [A B]. apply orb_false_iff in A; destruct A; subst.
    exploit update_labels_false; eauto. intros (C & D); subst.
    auto.
Qed.

Lemma ana_function_inv:
  forall f lm,
  ana_function f = Some lm -> ana_code lm false FStop f.(fn_code) = (lm, false).
Proof.
  intros. unfold ana_function in H.
  eapply PrimIter.iterate_prop with
    (Q := fun lm => ana_code lm false FStop (fn_code f) = (lm, false))
    (P := fun (lm: labelmap) => True); eauto.
  intros. unfold ana_iter.
  destruct (ana_code a false FStop (fn_code f)) as (lm1, ch1) eqn:ANA.
  destruct ch1. auto. exploit ana_code_false; eauto. intros [A B]. congruence. 
Qed.

Remark wt_ana_code_cons:
  forall f lm fs i c,
  ana_code lm false fs (i :: c) = (lm, false) ->
  wt_code f lm fs (i :: c) = true ->
  exists fs', ana_code lm false fs' c = (lm, false) /\ wt_code f lm fs' c = true.
Proof.
  simpl; intros; destruct i; InvBooleans; try (econstructor; split; eassumption).
- destruct (is_move_operation o l).
  InvBooleans; econstructor; eauto.
  destruct (type_of_operation o); InvBooleans; econstructor; eauto.
- destruct (update_label l fs lm) as [[fs1 lm1] ch1] eqn:UL. 
  exploit ana_code_false; eauto. intros [A B]; subst.
  exploit update_label_false; eauto. intros (C & D & E); subst.
  econstructor; eauto.
- destruct (update_label l fs lm) as [[fs1 lm1] ch1] eqn:UL. 
  exploit ana_code_false; eauto. intros [A B]; subst.
  econstructor; eauto.
- destruct (update_label l0 fs lm) as [[fs1 lm1] ch1] eqn:UL. 
  exploit ana_code_false; eauto. intros [A B]; subst.
  econstructor; eauto.
- destruct (update_labels l fs lm) as [lm1 ch1] eqn:UL. 
  exploit ana_code_false; eauto. intros [A B]; subst.
  econstructor; eauto.
Qed.

Lemma wt_find_label_rec:
  forall f lm lbl c' c fs,
  find_label lbl c = Some c' ->
  ana_code lm false fs c = (lm, false) ->
  wt_code f lm fs c = true ->
  ana_code lm false (PTree.get lbl lm) c' = (lm, false) /\ wt_code f lm (PTree.get lbl lm) c' = true.
Proof.
  induction c; intros.
- discriminate.
- simpl in H. specialize (is_label_correct lbl a). destruct (is_label lbl a); intros IL.
  + subst a. inv H. simpl in *. 
    destruct (update_label lbl fs lm) as [[fs1 lm1] ch1] eqn:UL.
    exploit ana_code_false; eauto. intros [A B]; subst.
    exploit update_label_false; eauto. intros (C & D & E). subst.
    InvBooleans. auto.
  + exploit wt_ana_code_cons; eauto. intros (fs' & A & B).
    eapply IHc; eauto. 
Qed.

Lemma wt_find_label:
  forall f lm lbl c,
  ana_function f = Some lm ->
  wt_funcode f lm = true ->
  find_label lbl f.(fn_code) = Some c ->
  ana_code lm false (PTree.get lbl lm) c = (lm, false) /\ wt_code f lm (PTree.get lbl lm) c = true.
Proof.
  intros. eapply wt_find_label_rec; eauto. apply ana_function_inv; auto. 
Qed.

(** * Soundness of the type system *)

Require Import Values.
Require Import Globalenvs.
Require Import Memory.

Module LSF := FSetFacts.Facts(Locset).

(** ** Typing the run-time state *)

Inductive wt_locset: singlefloats -> locset -> Prop :=
  | wt_locset_intro: forall s ls
      (TY: forall l, Val.has_type (ls l) (Loc.type l))
      (SINGLE: forall l, Locset.In l s -> Val.has_type (ls l) Tsingle),
    wt_locset (Some s) ls.

Lemma wt_mreg:
  forall fs ls r, wt_locset fs ls -> Val.has_type (ls (R r)) (mreg_type r).
Proof.
  intros. inv H. apply (TY (R r)). 
Qed.

Lemma wt_loc_type:
  forall fs ls l, wt_locset fs ls -> Val.has_type (ls l) (loc_type fs l).
Proof.
  intros. inv H. unfold loc_type, FSmem.
  destruct (typ_eq (Loc.type l) Tfloat); simpl; auto.
  destruct (Locset.mem l s) eqn:MEM; auto. 
  apply SINGLE. apply Locset.mem_2; auto.
Qed.

Lemma loc_type_subtype:
  forall fs l, subtype (loc_type fs l) (Loc.type l) = true.
Proof.
  unfold loc_type; intros. destruct (typ_eq (Loc.type l) Tfloat); simpl.
  rewrite e. destruct (FSmem l fs); auto. 
  destruct (Loc.type l); auto.
Qed.

Lemma wt_locset_top:
  forall ls,
  (forall l, Val.has_type (ls l) (Loc.type l)) -> 
  wt_locset FStop ls.
Proof.
  intros; constructor; intros. 
  auto.
  eelim Locset.empty_1; eauto.
Qed.

Lemma wt_locset_mon:
  forall fs1 fs2 ls,
  FSincl fs1 fs2 -> wt_locset fs1 ls -> wt_locset fs2 ls.
Proof.
  intros. inv H0; inv H. constructor; intros; auto. 
Qed.

Lemma wt_setreg:
  forall fs ls r v ty,
  Val.has_type v ty -> subtype ty (mreg_type r) = true -> wt_locset fs ls ->
  wt_locset (setreg fs r ty) (Locmap.set (R r) v ls).
Proof.
  intros. inv H1. constructor; intros. 
- unfold Locmap.set. destruct (Loc.eq (R r) l).
  subst l; simpl. eapply Val.has_subtype; eauto.
  destruct (Loc.diff_dec (R r) l); simpl; auto.
- unfold Locmap.set. destruct (Loc.eq (R r) l).
  destruct (typ_eq ty Tsingle). congruence. 
  subst l. rewrite LSF.remove_iff in H1. intuition.
  destruct (Loc.diff_dec (R r) l); simpl; auto.
  apply SINGLE. 
  destruct (typ_eq ty Tsingle).
  rewrite LSF.add_iff in H1; intuition.
  rewrite LSF.remove_iff in H1; intuition.
Qed.

Lemma wt_setregs:
  forall vl tyl rl fs rs,
  Val.has_type_list vl tyl ->
  subtype_list tyl (map mreg_type rl) = true ->
  wt_locset fs rs ->
  wt_locset (setregs fs rl tyl) (Locmap.setlist (map R rl) vl rs).
Proof.
  induction vl; simpl; intros.
- destruct tyl; try contradiction. destruct rl; try discriminate. 
  simpl. auto.
- destruct tyl as [ | ty tyl]; try contradiction. destruct H.
  destruct rl as [ | r rl]; simpl in H0; try discriminate. InvBooleans.
  simpl. eapply IHvl; eauto. eapply wt_setreg; eauto. 
Qed.

Lemma undef_regs_type:
  forall ty l rl ls,
  Val.has_type (ls l) ty -> Val.has_type (undef_regs rl ls l) ty.
Proof.
  induction rl; simpl; intros.
- auto.
- unfold Locmap.set. destruct (Loc.eq (R a) l). red; auto. 
  destruct (Loc.diff_dec (R a) l); auto. red; auto.
Qed.

Lemma wt_copyloc_gen:
  forall fs ls src dst temps,
  Val.has_type (ls src) (Loc.type dst) ->
  wt_locset fs ls ->
  wt_locset (copyloc fs dst src) (Locmap.set dst (ls src) (undef_regs temps ls)).
Proof.
  intros. inversion H0; subst. constructor; intros. 
- unfold Locmap.set. destruct (Loc.eq dst l).
  subst l. auto.
  destruct (Loc.diff_dec dst l); simpl; auto.
  apply undef_regs_type; auto.
- unfold Locmap.set. destruct (Loc.eq dst l).
  subst l. destruct (Locset.mem src s) eqn:E.
  apply SINGLE. apply Locset.mem_2; auto. 
  rewrite LSF.remove_iff in H1. intuition.
  destruct (Loc.diff_dec dst l); simpl; auto.
  apply undef_regs_type; auto.
  apply SINGLE.
  destruct (Locset.mem src s).
  rewrite LSF.add_iff in H1. intuition.
  rewrite LSF.remove_iff in H1. intuition.
Qed.

Lemma wt_copyloc:
  forall fs ls src dst temps,
  subtype (Loc.type src) (Loc.type dst) = true ->
  wt_locset fs ls ->
  wt_locset (copyloc fs dst src) (Locmap.set dst (ls src) (undef_regs temps ls)).
Proof.
  intros. eapply wt_copyloc_gen; eauto.
  eapply Val.has_subtype; eauto. inv H0; auto. 
Qed.

Lemma wt_undef_regs:
  forall fs ls temps, wt_locset fs ls -> wt_locset fs (undef_regs temps ls).
Proof.
  intros. inv H; constructor; intros.
- apply undef_regs_type; auto. 
- apply undef_regs_type; auto. 
Qed.

Lemma wt_call_regs:
  forall fs ls, wt_locset fs ls -> wt_locset FStop (call_regs ls).
Proof.
  intros. inv H. apply wt_locset_top; intros. 
  unfold call_regs. 
  destruct l; auto. 
  destruct sl; try exact I. 
  change (Loc.type (S Incoming pos ty)) with (Loc.type (S Outgoing pos ty)); auto.
Qed.

Remark destroyed_at_call_regs_charact:
  forall l,
  Locset.In l destroyed_at_call_regs <->
  match l with R r => In r destroyed_at_call | S _ _ _ => False end.
Proof.
  intros. unfold destroyed_at_call_regs. generalize destroyed_at_call. 
  induction l0; simpl.
- rewrite LSF.empty_iff. destruct l; tauto.
- rewrite LSF.add_iff. rewrite IHl0. destruct l; intuition congruence.
Qed.

Lemma wt_return_regs:
  forall fs caller fs' callee,
  wt_locset fs caller -> wt_locset fs' callee ->
  wt_locset (callregs fs) (return_regs caller callee).
Proof.
  intros. inv H; inv H0; constructor; intros.
- unfold return_regs. destruct l; auto. 
  destruct (in_dec mreg_eq r destroyed_at_call); auto.
- unfold callregs. 
  rewrite LSF.diff_iff in H. rewrite destroyed_at_call_regs_charact in H. destruct H.
  unfold return_regs. destruct l.
+ destruct (in_dec mreg_eq r destroyed_at_call). tauto. auto. 
+ auto.
Qed.

Lemma wt_init:
  forall s, wt_locset (Some s) (Locmap.init Vundef).
Proof.
  intros; constructor; intros; simpl; auto.
Qed.

Lemma callregs_setregs_result:
  forall sg fs,
  FSincl (setregs fs (loc_result sg) (proj_sig_res' sg)) (callregs fs).
Proof.
  assert (X: forall rl tyl, setregs None rl tyl = None).
  {
    induction rl; destruct tyl; simpl; auto. 
  }
  assert (Y: forall rl s tyl,
             exists s', setregs (Some s) rl tyl = Some s'
                     /\ forall l, Locset.In l s -> ~In l (map R rl) -> Locset.In l s').
  {
    induction rl; simpl; intros.
  - exists s; split. destruct tyl; auto. tauto.
  - destruct tyl. exists s; tauto. 
    destruct (IHrl (if typ_eq t Tsingle
                    then Locset.add (R a) s
                    else Locset.remove (R a) s) tyl) as (s1 & A & B).
    exists s1; split; auto. intros. apply B.
    destruct (typ_eq t Tsingle). 
    rewrite LSF.add_iff. tauto. 
    rewrite LSF.remove_iff. tauto.
    tauto.
  }
  intros. destruct fs as [s|]; simpl.
  - destruct (Y (loc_result sg) s (proj_sig_res' sg)) as (s' & A & B).
    rewrite A. constructor. red; intros.
    rewrite LSF.diff_iff in H. destruct H. apply B. auto. 
    red; intros. exploit list_in_map_inv; eauto. intros (r & U & V).
    subst a. elim H0. rewrite destroyed_at_call_regs_charact. 
    eapply loc_result_caller_save; eauto.
  - rewrite X. constructor.
Qed.

Definition wt_fundef (fd: fundef) :=
  match fd with
  | Internal f => wt_function f = true
  | External ef => True
  end.

Inductive wt_callstack: list stackframe -> singlefloats -> Prop :=
  | wt_callstack_nil: forall s,
      wt_callstack nil (Some s)
  | wt_callstack_cons: forall f sp rs c s fs lm fs0 fs1
        (WTSTK: wt_callstack s fs0)
        (ANF: ana_function f = Some lm)
        (WTF: wt_funcode f lm = true)
        (ANC: ana_code lm false (callregs fs1) c = (lm, false))
        (WTC: wt_code f lm (callregs fs1) c = true)
        (WTRS: wt_locset fs rs)
        (INCL: FSincl (callregs fs) (callregs fs1)),
      wt_callstack (Stackframe f sp rs c :: s) fs.

Lemma wt_parent_locset:
  forall s fs, wt_callstack s fs -> wt_locset fs (parent_locset s).
Proof.
  induction 1; simpl.
- apply wt_init.
- auto.
Qed.

Lemma wt_callstack_change_fs:
  forall s fs, wt_callstack s fs -> wt_callstack s (callregs fs).
Proof.
  induction 1.
- constructor. 
- econstructor; eauto. 
  apply wt_locset_mon with fs; auto.
  + destruct fs; simpl; constructor.
    red; intros. eapply Locset.diff_1; eauto. 
  + inv INCL; simpl; constructor.
    destruct fs; simpl in H0; inv H0. 
    red; intros. exploit H2; eauto. rewrite ! LSF.diff_iff. tauto.
Qed.

Inductive wt_state: state -> Prop :=
  | wt_regular_state: forall s f sp c rs m lm fs fs0
        (WTSTK: wt_callstack s fs0)
        (ANF: ana_function f = Some lm)
        (WTF: wt_funcode f lm = true)
        (ANC: ana_code lm false fs c = (lm, false))
        (WTC: wt_code f lm fs c = true)
        (WTRS: wt_locset fs rs),
      wt_state (State s f sp c rs m)
  | wt_call_state: forall s fd rs m fs
        (WTSTK: wt_callstack s fs)
        (WTFD: wt_fundef fd)
        (WTRS: wt_locset fs rs),
      wt_state (Callstate s fd rs m)
  | wt_return_state: forall s rs m fs
        (WTSTK: wt_callstack s fs)
        (WTRS: wt_locset (callregs fs) rs),
      wt_state (Returnstate s rs m).

(** ** Preservation of state typing by transitions *)

Section SOUNDNESS.

Variable prog: program.
Let ge := Genv.globalenv prog.

Hypothesis wt_prog:
  forall i fd, In (i, Gfun fd) prog.(prog_defs) -> wt_fundef fd.

Lemma wt_find_function:
  forall ros rs f, find_function ge ros rs = Some f -> wt_fundef f.
Proof.
  intros. 
  assert (X: exists i, In (i, Gfun f) prog.(prog_defs)).
  {
    destruct ros as [r | s]; simpl in H.
    eapply Genv.find_funct_inversion; eauto. 
    destruct (Genv.find_symbol ge s) as [b|]; try discriminate.
    eapply Genv.find_funct_ptr_inversion; eauto.
  }
  destruct X as [i IN]. eapply wt_prog; eauto. 
Qed.

Theorem step_type_preservation:
  forall S1 t S2, step ge S1 t S2 -> wt_state S1 -> wt_state S2.
Proof.
  induction 1; intros WTS; inv WTS.
- (* getstack *)
  simpl in *; InvBooleans. 
  econstructor; eauto.
  apply wt_copyloc; auto.
- (* setstack *)
  simpl in *; InvBooleans. 
  econstructor; eauto.
  apply wt_copyloc_gen; auto.
  eapply Val.has_subtype; eauto. eapply wt_loc_type; eauto.
- (* op *)
  simpl in *. destruct (is_move_operation op args) as [src | ] eqn:ISMOVE.
  + (* move *)
    InvBooleans. exploit is_move_operation_correct; eauto. intros [EQ1 EQ2]; subst. 
    simpl in H. inv H.
    econstructor; eauto. 
    apply wt_copyloc; auto. simpl. rewrite H0. 
    destruct (mreg_type res); auto.
  + (* other ops *) 
    destruct (type_of_operation op) as [ty_args ty_res] eqn:TYOP. InvBooleans.
    econstructor; eauto.
    apply wt_setreg; auto. 
    change ty_res with (snd (ty_args, ty_res)). rewrite <- TYOP. 
    eapply type_of_operation_sound; eauto. 
    red; intros; subst op. simpl in ISMOVE. 
    destruct args; try discriminate. destruct args; discriminate. 
    apply wt_undef_regs; auto.
- (* load *)
  simpl in *; InvBooleans. 
  econstructor; eauto.
  apply wt_setreg. 
  destruct a; simpl in H0; try discriminate. eapply Mem.load_type; eauto.
  auto. 
  apply wt_undef_regs; auto.
- (* store *)
  simpl in *; InvBooleans. 
  econstructor; eauto.
  apply wt_undef_regs; auto.
- (* call *)
  simpl in *; InvBooleans.
  econstructor; eauto. econstructor; eauto.
  destruct (callregs fs); constructor. red; auto. 
  eapply wt_find_function; eauto.
- (* tailcall *)
  simpl in *; InvBooleans.
  econstructor. apply wt_callstack_change_fs; eauto. 
  eapply wt_find_function; eauto.
  eapply wt_return_regs. apply wt_parent_locset; auto. eauto.
- (* builtin *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  apply wt_setregs. 
  eapply external_call_well_typed'; eauto.
  auto.
  apply wt_undef_regs; auto.
- (* annot *)
  simpl in *; InvBooleans.
  econstructor; eauto. 
- (* label *)
  simpl in *.
  destruct (update_label lbl fs lm) as [[fs1 lm1] ch1] eqn:UL.
  exploit ana_code_false; eauto. intros [A B]; subst.
  exploit update_label_false; eauto. intros (A & B & C); subst.
  econstructor; eauto.
  eapply wt_locset_mon; eauto.
- (* goto *)
  simpl in *.
  destruct (update_label lbl fs lm) as [[fs1 lm1] ch1] eqn:UL.
  exploit ana_code_false; eauto. intros [A B]; subst.
  exploit update_label_false; eauto. intros (A & B & C); subst.
  exploit wt_find_label; eauto. intros [P Q].
  econstructor; eauto. 
  eapply wt_locset_mon; eauto.
- (* cond branch, taken *)
  simpl in *.
  destruct (update_label lbl fs lm) as [[fs1 lm1] ch1] eqn:UL.
  exploit ana_code_false; eauto. intros [A B]; subst.
  exploit update_label_false; eauto. intros (A & B & C); subst.
  exploit wt_find_label; eauto. intros [P Q].
  econstructor; eauto. 
  eapply wt_locset_mon. eauto. 
  apply wt_undef_regs; auto.
- (* cond branch, not taken *)
  simpl in *.
  destruct (update_label lbl fs lm) as [[fs1 lm1] ch1] eqn:UL.
  exploit ana_code_false; eauto. intros [A B]; subst.
  exploit update_label_false; eauto. intros (A & B & C); subst.
  econstructor. eauto. eauto. eauto. eauto. eauto.  
  apply wt_undef_regs; auto.
- (* jumptable *)
  simpl in *.
  destruct (update_labels tbl fs lm) as [lm1 ch1] eqn:UL.
  exploit ana_code_false; eauto. intros [A B]; subst.
  exploit update_labels_false; eauto. intros (A & B); subst.
  exploit wt_find_label; eauto. intros [P Q].
  econstructor; eauto.
  apply wt_undef_regs. eapply wt_locset_mon; eauto. apply A. eapply list_nth_z_in; eauto. 
- (* return *)
  econstructor. eauto. 
  eapply wt_return_regs. 
  apply wt_parent_locset; auto.
  eauto.
- (* internal function *)
  simpl in WTFD. unfold wt_function in WTFD.
  destruct (ana_function f) as [lm|] eqn:ANF; try discriminate.
  econstructor. eauto. eauto. eauto. apply ana_function_inv; auto. exact WTFD. 
  apply wt_undef_regs. eapply wt_call_regs; eauto. 
- (* external function *)
  econstructor. eauto. 
  eapply wt_locset_mon.
  eapply callregs_setregs_result. 
  eapply wt_setregs.
  eapply external_call_well_typed'; eauto.
  unfold proj_sig_res', loc_result. destruct (sig_res (ef_sig ef) )as [[] | ]; auto.
  auto.
- (* return *)
  inv WTSTK. econstructor; eauto. 
  apply wt_locset_mon with (callregs fs); auto. 
Qed.

Theorem wt_initial_state:
  forall S, initial_state prog S -> wt_state S.
Proof.
  induction 1. econstructor. 
  apply wt_callstack_nil with (s := Locset.empty). 
  unfold ge0 in H1. exploit Genv.find_funct_ptr_inversion; eauto.
  intros [id IN]. eapply wt_prog; eauto. 
  apply wt_init.
Qed.

End SOUNDNESS.

(** Properties of well-typed states that are used in [Stackingproof]. *)

Lemma wt_state_getstack:
  forall s f sp sl ofs ty rd c rs m,
  wt_state (State s f sp (Lgetstack sl ofs ty rd :: c) rs m) ->
  slot_valid f sl ofs ty = true.
Proof.
  intros. inv H. simpl in WTC; InvBooleans. auto.
Qed.

Lemma wt_state_setstack:
  forall s f sp sl ofs ty r c rs m,
  wt_state (State s f sp (Lsetstack r sl ofs ty :: c) rs m) ->
  Val.has_type (rs (R r)) ty /\ slot_valid f sl ofs ty = true /\ slot_writable sl = true.
Proof.
  intros. inv H. simpl in WTC; InvBooleans. intuition. 
  eapply Val.has_subtype; eauto. eapply wt_loc_type; eauto. 
Qed.

Lemma wt_state_tailcall:
  forall s f sp sg ros c rs m,
  wt_state (State s f sp (Ltailcall sg ros :: c) rs m) ->
  size_arguments sg = 0.
Proof.
  intros. inv H. simpl in WTC; InvBooleans. auto.
Qed.

Lemma wt_state_annot:
  forall s f sp ef args c rs m,
  wt_state (State s f sp (Lannot ef args :: c) rs m) ->
  forallb (loc_valid f) args = true.
Proof.
  intros. inv H. simpl in WTC; InvBooleans. auto. 
Qed.

Lemma wt_callstate_wt_regs:
  forall s f rs m,
  wt_state (Callstate s f rs m) ->
  forall r, Val.has_type (rs (R r)) (mreg_type r).
Proof.
  intros. inv H. eapply wt_mreg; eauto.
Qed.

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

(** At each program point, we infer a set of machine registers
  that are guaranteed to contain single-precision floats.
  The inference is a simple forward dataflow analysis, iterating on the 
  list of instructions until a fixpoint is reached.  The result of
  the analysis is a map from labels to sets of machine registers
  containing single-precision floats.  *)

Module OrderedMreg := OrderedIndexed(IndexedMreg).
Module Regset := FSetAVL.Make(OrderedMreg).

Definition setreg (fs: Regset.t) (r: mreg) (t: typ) :=
  if typ_eq t Tsingle then Regset.add r fs else Regset.remove r fs.

Fixpoint setregs (fs: Regset.t) (rl: list mreg) (tl: list typ) :=
  match rl, tl with
  | nil, nil => fs
  | r1 :: rs, t1 :: ts => setregs (setreg fs r1 t1) rs ts
  | _, _ => fs
  end.

Definition copyreg (fs: Regset.t) (rd rs: mreg) :=
  if Regset.mem rs fs then Regset.add rd fs else Regset.remove rd fs.

Definition allregs :=
  List.fold_right Regset.add Regset.empty
                  (float_caller_save_regs ++ float_callee_save_regs).

Definition destroyed_at_call_regs :=
  List.fold_right Regset.add Regset.empty destroyed_at_call.

Definition callregs (fs: Regset.t) :=
  Regset.diff fs destroyed_at_call_regs.

Definition labelmap := PMap.t Regset.t.

Definition update_label (lbl: label) (fs: Regset.t) (lm: labelmap) : Regset.t * labelmap * bool :=
  let fs1 := PMap.get lbl lm in
  if Regset.subset fs1 fs
  then (fs1, lm, false)
  else let fs2 := Regset.inter fs fs1 in (fs2, PMap.set lbl fs2 lm, true).

Fixpoint update_labels (lbls: list label) (fs: Regset.t) (lm: labelmap): labelmap * bool :=
  match lbls with
  | nil => (lm, false)
  | lbl1 :: lbls =>
      let '(fs1, lm1, changed1) := update_label lbl1 fs lm in
      let '(lm2, changed2) := update_labels lbls fs lm1 in
      (lm2, changed1 || changed2)
  end.

Fixpoint ana_code (lm: labelmap) (ch: bool) (fs: Regset.t) (c: code) : labelmap * bool :=
  match c with
  | nil => (lm, ch)
  | Lgetstack sl ofs ty rd :: c =>
      ana_code lm ch (setreg fs rd ty) c
  | Lsetstack rs sl ofs ty :: c =>
      ana_code lm ch fs c
  | Lop op args dst :: c =>
      match is_move_operation op args with
      | Some src => ana_code lm ch (copyreg fs dst src) c
      | None     => ana_code lm ch (setreg fs dst (snd (type_of_operation op))) c
      end
  | Lload chunk addr args dst :: c =>
      ana_code lm ch (setreg fs dst (type_of_chunk chunk)) c
  | Lstore chunk addr args src :: c =>
      ana_code lm ch fs c
  | Lcall sg ros :: c =>
      ana_code lm ch (callregs fs) c
  | Ltailcall sg ros :: c =>
      ana_code lm ch allregs c
  | Lbuiltin ef args res :: c =>
      ana_code lm ch (setregs fs res (proj_sig_res' (ef_sig ef))) c
  | Lannot ef args :: c =>
      ana_code lm ch fs c
  | Llabel lbl :: c =>
      let '(fs1, lm1, ch1) := update_label lbl fs lm in
      ana_code lm1 (ch || ch1) fs1 c
  | Lgoto lbl :: c =>
      let '(fs1, lm1, ch1) := update_label lbl fs lm in
      ana_code lm1 (ch || ch1) allregs c
  | Lcond cond args lbl :: c =>
      let '(fs1, lm1, ch1) := update_label lbl fs lm in
      ana_code lm1 (ch || ch1) fs c
  | Ljumptable r lbls :: c =>
      let '(lm1, ch1) := update_labels lbls fs lm in
      ana_code lm1 (ch || ch1) allregs c
  | Lreturn :: c =>
      ana_code lm ch allregs c
  end.

Definition ana_iter (c: code) (lm: labelmap) : labelmap + labelmap :=
  let '(lm1, ch) := ana_code lm false Regset.empty c in
  if ch then inr _ lm1 else inl _ lm.

Definition ana_function (f: function): option (PMap.t Regset.t) :=
  PrimIter.iterate _ _ (ana_iter f.(fn_code)) (PMap.init allregs).

(** * The type-checker *)

(** The typing rules are presented as boolean-valued functions so that we
  get an executable type-checker for free. *)

Section WT_INSTR.

Variable funct: function.

Variable lm: labelmap.

Definition reg_type (fs: Regset.t) (r: mreg) :=
  let ty := mreg_type r in
  if typ_eq ty Tfloat && Regset.mem r fs then Tsingle else ty.

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

Fixpoint wt_code (fs: Regset.t) (c: code) : bool :=
  match c with
  | nil => true
  | Lgetstack sl ofs ty rd :: c =>
      subtype ty (mreg_type rd) && slot_valid sl ofs ty &&
      wt_code (setreg fs rd ty) c
  | Lsetstack rs sl ofs ty :: c =>
      subtype (reg_type fs rs) ty &&
      slot_valid sl ofs ty && slot_writable sl &&
      wt_code fs c
  | Lop op args dst :: c =>
      match is_move_operation op args with
      | Some src =>
          typ_eq (mreg_type src) (mreg_type dst) &&
          wt_code (copyreg fs dst src) c
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
      wt_code allregs c
  | Lbuiltin ef args res :: c =>
      let ty_res := proj_sig_res' (ef_sig ef) in
      subtype_list ty_res (map mreg_type res) &&
      wt_code (setregs fs res ty_res) c
  | Lannot ef args :: c =>
      forallb loc_valid args &&
      wt_code fs c
  | Llabel lbl :: c =>
      let fs1 := PMap.get lbl lm in
      Regset.subset fs1 fs && wt_code fs1 c
  | Lgoto lbl :: c =>
      let fs1 := PMap.get lbl lm in
      Regset.subset fs1 fs && wt_code allregs c
  | Lcond cond args lbl :: c =>
      let fs1 := PMap.get lbl lm in
      Regset.subset fs1 fs && wt_code fs c
  | Ljumptable r lbls :: c =>
      forallb (fun lbl => Regset.subset (PMap.get lbl lm) fs) lbls &&
      wt_code allregs c
  | Lreturn :: c =>
      wt_code allregs c
  end.

Remark wt_code_cons:
  forall fs i c,
  wt_code fs (i :: c) = true -> exists fs', wt_code fs' c = true.
Proof.
  simpl; intros. destruct i; InvBooleans; try (econstructor; eassumption).
  destruct (is_move_operation o l).
  InvBooleans; econstructor; eassumption.
  destruct (type_of_operation o). InvBooleans; econstructor; eassumption.
Qed.

Lemma wt_find_label:
  forall lbl c' c fs,
  find_label lbl c = Some c' ->
  wt_code fs c = true ->
  wt_code (PMap.get lbl lm) c' = true.
Proof.
  induction c; intros.
- discriminate.
- simpl in H. specialize (is_label_correct lbl a). destruct (is_label lbl a); intros IL.
  + subst a. simpl in H0. inv H. InvBooleans. auto. 
  + destruct (wt_code_cons _ _ _ H0) as [fs' WT]. eauto. 
Qed.

End WT_INSTR.

Definition wt_funcode (f: function) (lm: labelmap) : bool :=
  wt_code f lm Regset.empty f.(fn_code).

Definition wt_function (f: function) : bool :=
  match ana_function f with
  | None => false
  | Some lm => wt_funcode f lm
  end.

(** * Soundness of the type system *)

Require Import Values.
Require Import Globalenvs.
Require Import Memory.

Module RSF := FSetFacts.Facts(Regset).

(** ** Typing the run-time state *)

Definition loc_type (fs: Regset.t) (l: loc): typ :=
  match l with
  | R r => reg_type fs r
  | S sl ofs ty => ty
  end.

Definition wt_locset (fs: Regset.t) (ls: locset) : Prop :=
  forall l, Val.has_type (ls l) (loc_type fs l).

Remark subtype_refl:
  forall ty, subtype ty ty = true.
Proof.
  destruct ty; reflexivity.
Qed.

Remark reg_type_sub:
  forall fs r, subtype (reg_type fs r) (mreg_type r) = true.
Proof.
  intros. unfold reg_type. destruct (typ_eq (mreg_type r) Tfloat); simpl.
  rewrite e. destruct (Regset.mem r fs); auto. 
  apply subtype_refl.
Qed.

Lemma wt_mreg:
  forall fs ls r, wt_locset fs ls -> Val.has_type (ls (R r)) (mreg_type r).
Proof.
  intros. eapply Val.has_subtype. apply reg_type_sub with (fs := fs). apply H.
Qed.

Lemma wt_locset_empty:
  forall ls,
  (forall l, Val.has_type (ls l) (Loc.type l)) -> 
  wt_locset Regset.empty ls.
Proof.
  intros; red; intros. destruct l; simpl.
- unfold reg_type. change (Regset.mem r Regset.empty) with false. 
  rewrite andb_false_r. apply H. 
- apply H.
Qed.

Remark reg_type_mon:
  forall fs1 fs2 r, Regset.Subset fs2 fs1 -> subtype (reg_type fs1 r) (reg_type fs2 r) = true.
Proof.
  intros. unfold reg_type. destruct (typ_eq (mreg_type r) Tfloat); simpl.
  rewrite e. destruct (Regset.mem r fs2) eqn:E. 
  rewrite Regset.mem_1. auto. apply H. apply Regset.mem_2; auto. 
  destruct (Regset.mem r fs1); auto. 
  apply subtype_refl.
Qed.

Lemma wt_locset_mon:
  forall fs1 fs2 ls,
  Regset.Subset fs2 fs1 -> wt_locset fs1 ls -> wt_locset fs2 ls.
Proof.
  intros; red; intros. apply Val.has_subtype with (loc_type fs1 l); auto. 
  unfold loc_type. destruct l. apply reg_type_mon; auto. apply subtype_refl.
Qed.

Lemma wt_setreg:
  forall fs ls r v ty,
  Val.has_type v ty -> subtype ty (mreg_type r) = true -> wt_locset fs ls ->
  wt_locset (setreg fs r ty) (Locmap.set (R r) v ls).
Proof.
  intros; red; intros.
  unfold Locmap.set. destruct (Loc.eq (R r) l).
- subst l. simpl. unfold reg_type, setreg.
  destruct (typ_eq (mreg_type r) Tfloat &&
      Regset.mem r
        (if typ_eq ty Tsingle then Regset.add r fs else Regset.remove r fs)) eqn:E.
+ InvBooleans. destruct (typ_eq ty Tsingle).
  congruence.
  rewrite RSF.remove_b in H3. unfold RSF.eqb in H3. rewrite dec_eq_true in H3. 
  simpl in H3. rewrite andb_false_r in H3. discriminate.
+ eapply Val.has_subtype; eauto.
- destruct (Loc.diff_dec (R r) l).
+ replace (loc_type (setreg fs r ty) l) with (loc_type fs l).
  apply H1. 
  unfold loc_type, setreg. destruct l; auto. destruct (typ_eq ty Tsingle).
  unfold reg_type. rewrite RSF.add_neq_b. auto. congruence. 
  unfold reg_type. rewrite RSF.remove_neq_b. auto. congruence.
+ red; auto. 
Qed.

Lemma wt_copyreg:
  forall fs ls src dst v,
  mreg_type src = mreg_type dst ->
  wt_locset fs ls ->
  Val.has_type v (reg_type fs src) ->
  wt_locset (copyreg fs dst src) (Locmap.set (R dst) v ls).
Proof.
  intros; red; intros.
  unfold Locmap.set. destruct (Loc.eq (R dst) l). 
- subst l. simpl. unfold reg_type, copyreg.
  unfold reg_type in H1. rewrite H in H1. 
  destruct (Regset.mem src fs) eqn:SRC. 
  rewrite RSF.add_b. unfold RSF.eqb. rewrite dec_eq_true. simpl. auto.
  rewrite RSF.remove_b. unfold RSF.eqb. rewrite dec_eq_true. simpl. rewrite ! andb_false_r. 
  rewrite andb_false_r in H1. auto.
- destruct (Loc.diff_dec (R dst) l). 
+ replace (loc_type (copyreg fs dst src) l) with (loc_type fs l).
  apply H0.
  unfold loc_type, copyreg. destruct l; auto. destruct (Regset.mem src fs). 
  unfold reg_type. rewrite RSF.add_neq_b. auto. congruence. 
  unfold reg_type. rewrite RSF.remove_neq_b. auto. congruence.
+ red; auto.
Qed.

Lemma wt_setstack:
  forall fs ls sl ofs ty v,
  Val.has_type v ty -> wt_locset fs ls ->
  wt_locset fs (Locmap.set (S sl ofs ty) v ls).
Proof.
  intros; red; intros.
  unfold Locmap.set. 
  destruct (Loc.eq (S sl ofs ty) l).
  subst l. simpl. auto. 
  destruct (Loc.diff_dec (S sl ofs ty) l). auto. red. auto.
Qed.

Lemma wt_undef:
  forall fs ls l, wt_locset fs ls -> wt_locset fs (Locmap.set l Vundef ls).
Proof.
  intros; red; intros. unfold Locmap.set. 
  destruct (Loc.eq l l0). red; auto. 
  destruct (Loc.diff_dec l l0); auto. red; auto.
Qed.

Lemma wt_undef_regs:
  forall fs rs ls, wt_locset fs ls -> wt_locset fs (undef_regs rs ls).
Proof.
  induction rs; simpl; intros. auto. apply wt_undef; auto. 
Qed.

Lemma wt_call_regs:
  forall fs ls, wt_locset fs ls -> wt_locset Regset.empty (call_regs ls).
Proof.
  intros; red; intros. unfold call_regs. destruct l.
  eapply Val.has_subtype; eauto. unfold loc_type. apply reg_type_mon. 
  red; intros. eelim Regset.empty_1; eauto. 
  destruct sl.
  red; auto.
  change (loc_type Regset.empty (S Incoming pos ty))
    with (loc_type fs (S Outgoing pos ty)). auto.
  red; auto.
Qed.

Remark set_from_list:
  forall r l, Regset.In r (List.fold_right Regset.add Regset.empty l) <-> In r l.
Proof.
  induction l; simpl. 
- rewrite RSF.empty_iff. tauto.
- rewrite RSF.add_iff. rewrite IHl. tauto.
Qed.

Lemma wt_return_regs:
  forall fs caller callee,
  wt_locset fs caller -> wt_locset Regset.empty callee ->
  wt_locset (callregs fs) (return_regs caller callee).
Proof.
  intros; red; intros.
  unfold return_regs. destruct l.
- destruct (in_dec mreg_eq r destroyed_at_call). 
+ unfold loc_type. replace (reg_type (callregs fs) r) with (mreg_type r).
  eapply Val.has_subtype. eapply reg_type_sub. apply (H0 (R r)).
  unfold reg_type, callregs. rewrite RSF.diff_b. 
  rewrite (@Regset.mem_1 destroyed_at_call_regs).
  rewrite ! andb_false_r. auto.
  unfold destroyed_at_call_regs; apply set_from_list; auto.
+ unfold loc_type, reg_type, callregs. rewrite RSF.diff_b. 
  destruct (Regset.mem r destroyed_at_call_regs) eqn:E. 
  elim n. apply set_from_list. apply Regset.mem_2; auto. 
  rewrite andb_true_r. apply H. 
- unfold loc_type. apply H. 
Qed.

Lemma wt_init:
  forall fs, wt_locset fs (Locmap.init Vundef).
Proof.
  red; intros. unfold Locmap.init. red; auto.
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

Lemma wt_setregs_result:
  forall sg fs v rl rs,
  Val.has_type v (proj_sig_res sg) ->
  subtype_list (proj_sig_res' sg) (map mreg_type rl) = true ->
  wt_locset fs rs ->
  wt_locset (setregs fs rl (proj_sig_res' sg)) 
            (Locmap.setlist (map R rl) (encode_long (sig_res sg) v) rs).
Proof.
  intros. eapply wt_setregs; eauto. 
  unfold proj_sig_res in H. unfold encode_long, proj_sig_res'. 
  destruct (sig_res sg) as [[] | ]; simpl; intuition. 
  destruct v; simpl; auto.
  destruct v; simpl; auto.
Qed.

Remark in_setreg_other:
  forall fs r ty r',
  r' <> r -> (Regset.In r' (setreg fs r ty) <-> Regset.In r' fs).
Proof.
  intros. unfold setreg. destruct (typ_eq ty Tsingle). 
  rewrite RSF.add_iff. intuition. 
  rewrite RSF.remove_iff. intuition.
Qed.

Remark in_setregs_other:
  forall r rl fs tyl,
  ~In r rl -> (Regset.In r (setregs fs rl tyl) <-> Regset.In r fs).
Proof.
  induction rl; simpl; intros. 
- destruct tyl; tauto.
- destruct tyl. tauto. rewrite IHrl by tauto. apply in_setreg_other. intuition.
Qed. 

Remark callregs_setregs_result:
  forall sg fs,
  Regset.Subset (callregs fs) (setregs fs (loc_result sg) (proj_sig_res' sg)).
Proof.
  red; unfold callregs; intros. rewrite RSF.diff_iff in H. destruct H. 
  apply in_setregs_other; auto. 
  red; intros; elim H0. apply set_from_list. eapply loc_result_caller_save; eauto.
Qed.

Definition wt_fundef (fd: fundef) :=
  match fd with
  | Internal f => wt_function f = true
  | External ef => True
  end.

Inductive wt_callstack: list stackframe -> Regset.t -> Prop :=
  | wt_callstack_nil: forall fs, 
      wt_callstack nil fs
  | wt_callstack_cons: forall f sp rs c s fs lm fs0 fs1
        (WTSTK: wt_callstack s fs0)
        (WTF: wt_funcode f lm = true)
        (WTC: wt_code f lm (callregs fs1) c = true)
        (WTRS: wt_locset fs rs)
        (INCL: Regset.Subset (callregs fs1) (callregs fs)),
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
  unfold callregs; red; intros. eapply Regset.diff_1; eauto.
  red; intros. exploit INCL; eauto. unfold callregs. rewrite ! RSF.diff_iff. 
  tauto.
Qed.

Inductive wt_state: state -> Prop :=
  | wt_regular_state: forall s f sp c rs m lm fs fs0
        (WTSTK: wt_callstack s fs0)
        (WTF: wt_funcode f lm = true)
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
  simpl in WTC; InvBooleans. 
  econstructor; eauto.
  apply wt_setreg; auto. apply (WTRS (S sl ofs ty)). apply wt_undef_regs; auto.
- (* setstack *)
  simpl in WTC; InvBooleans. 
  econstructor; eauto. 
  apply wt_setstack; auto. eapply Val.has_subtype; eauto. apply WTRS. 
  apply wt_undef_regs; auto.
- (* op *)
  simpl in WTC. destruct (is_move_operation op args) as [src | ] eqn:ISMOVE.
  + (* move *)
    InvBooleans. exploit is_move_operation_correct; eauto. intros [EQ1 EQ2]; subst. 
    simpl in H. inv H.
    econstructor; eauto. 
    apply wt_copyreg. auto. apply wt_undef_regs; auto. apply WTRS. 
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
  simpl in WTC; InvBooleans. 
  econstructor; eauto.
  apply wt_setreg. 
  destruct a; simpl in H0; try discriminate. eapply Mem.load_type; eauto.
  auto. 
  apply wt_undef_regs; auto.
- (* store *)
  simpl in WTC; InvBooleans. 
  econstructor; eauto.
  apply wt_undef_regs; auto.
- (* call *)
  simpl in WTC; InvBooleans.
  econstructor; eauto. econstructor; eauto.
  red; auto.
  eapply wt_find_function; eauto.
- (* tailcall *)
  simpl in WTC; InvBooleans.
  econstructor. apply wt_callstack_change_fs; eauto. 
  eapply wt_find_function; eauto.
  apply wt_return_regs. apply wt_parent_locset; auto. 
  eapply wt_locset_mon; eauto. red; intros. eelim Regset.empty_1; eauto.
- (* builtin *)
  simpl in WTC; InvBooleans. inv H. 
  econstructor; eauto.
  apply wt_setregs_result; auto.
  eapply external_call_well_typed; eauto.
  apply wt_undef_regs; auto.
- (* annot *)
  simpl in WTC; InvBooleans.
  econstructor; eauto. 
- (* label *)
  simpl in WTC; InvBooleans. 
  econstructor; eauto.
  eapply wt_locset_mon; eauto. apply Regset.subset_2; auto.
- (* goto *)
  simpl in WTC; InvBooleans. 
  econstructor. eauto. eauto. 
  eapply wt_find_label; eauto. 
  eapply wt_locset_mon; eauto. apply Regset.subset_2; auto.
- (* cond branch, taken *)
  simpl in WTC; InvBooleans. 
  econstructor. eauto. eauto. 
  eapply wt_find_label; eauto. 
  eapply wt_locset_mon. apply Regset.subset_2; eauto.
  apply wt_undef_regs; auto.
- (* cond branch, not taken *)
  simpl in WTC; InvBooleans. 
  econstructor. eauto. eauto. eauto. 
  apply wt_undef_regs; auto.
- (* jumptable *)
  simpl in WTC; InvBooleans. 
  econstructor. eauto. eauto.
  eapply wt_find_label; eauto. 
  apply wt_locset_mon with fs.
  apply Regset.subset_2. rewrite List.forallb_forall in H2. apply H2. 
  eapply list_nth_z_in; eauto.
  apply wt_undef_regs; auto.
- (* return *)
  econstructor. eauto. 
  apply wt_return_regs. 
  apply wt_parent_locset; auto. 
  apply wt_locset_mon with fs; auto. red; intros. eelim Regset.empty_1; eauto.
- (* internal function *)
  simpl in WTFD. unfold wt_function in WTFD. destruct (ana_function f) as [lm|]; try discriminate.
  econstructor. eauto. eauto. eexact WTFD. 
  apply wt_undef_regs. eapply wt_call_regs; eauto. 
- (* external function *)
  inv H0. 
  econstructor. eauto. 
  eapply wt_locset_mon. 2: eapply wt_setregs_result; eauto. 
  apply callregs_setregs_result. 
  eapply external_call_well_typed; eauto. 
  unfold proj_sig_res', loc_result. destruct (sig_res (ef_sig ef) )as [[] | ]; auto.
- (* return *)
  inv WTSTK. econstructor; eauto. 
  apply wt_locset_mon with (callregs fs); auto. 
Qed.

Theorem wt_initial_state:
  forall S, initial_state prog S -> wt_state S.
Proof.
  induction 1. econstructor. 
  apply wt_callstack_nil with (fs := Regset.empty).
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
  eapply Val.has_subtype; eauto. apply WTRS. 
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

Lemma wt_callstate_wt_locset:
  forall s f rs m,
  wt_state (Callstate s f rs m) -> wt_locset Regset.empty rs.
Proof.
  intros. inv H. apply wt_locset_mon with fs; auto. 
  red; intros; eelim Regset.empty_1; eauto.
Qed.


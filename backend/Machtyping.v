(** Type system for the Mach intermediate language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Mem.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Conventions.
Require Import Mach.

(** * Typing rules *)

Inductive wt_instr : instruction -> Prop :=
  | wt_Mlabel:
     forall lbl,
     wt_instr (Mlabel lbl)
  | wt_Mgetstack:
     forall ofs ty r,
     mreg_type r = ty ->
     wt_instr (Mgetstack ofs ty r)
  | wt_Msetstack:
     forall ofs ty r,
     mreg_type r = ty -> 24 <= Int.signed ofs ->
     wt_instr (Msetstack r ofs ty)
  | wt_Mgetparam:
     forall ofs ty r,
     mreg_type r = ty ->
     wt_instr (Mgetparam ofs ty r)
  | wt_Mopmove:
     forall r1 r,
     mreg_type r1 = mreg_type r ->
     wt_instr (Mop Omove (r1 :: nil) r)
  | wt_Mopundef:
     forall r,
     wt_instr (Mop Oundef nil r)
  | wt_Mop:
     forall op args res,
      op <> Omove -> op <> Oundef ->
      (List.map mreg_type args, mreg_type res) = type_of_operation op ->
      wt_instr (Mop op args res)
  | wt_Mload:
      forall chunk addr args dst,
      List.map mreg_type args = type_of_addressing addr ->
      mreg_type dst = type_of_chunk chunk ->
      wt_instr (Mload chunk addr args dst)
  | wt_Mstore:
      forall chunk addr args src,
      List.map mreg_type args = type_of_addressing addr ->
      mreg_type src = type_of_chunk chunk ->
      wt_instr (Mstore chunk addr args src)
  | wt_Mcall:
      forall sig ros,
      match ros with inl r => mreg_type r = Tint | inr s => True end ->
      wt_instr (Mcall sig ros)
  | wt_Mgoto:
      forall lbl,
      wt_instr (Mgoto lbl)
  | wt_Mcond:
      forall cond args lbl,
      List.map mreg_type args = type_of_condition cond ->
      wt_instr (Mcond cond args lbl)
  | wt_Mreturn: 
      wt_instr Mreturn.

Record wt_function (f: function) : Prop := mk_wt_function {
  wt_function_instrs:
    forall instr, In instr f.(fn_code) -> wt_instr instr;
  wt_function_stacksize:
    f.(fn_stacksize) >= 0;
  wt_function_framesize:
    f.(fn_framesize) >= 24;
  wt_function_no_overflow:
    f.(fn_framesize) <= -Int.min_signed
}.

Definition wt_program (p: program) : Prop :=
  forall i f, In (i, f) (prog_funct p) -> wt_function f.

(** * Type soundness *)

Require Import Machabstr.

(** We show a weak type soundness result for the alternate semantics
    of Mach: for a well-typed Mach program, if a transition is taken
    from a state where registers hold values of their static types,
    registers in the final state hold values of their static types
    as well.  This is a progress theorem for our type system.
    It is used in the proof of implcation from the abstract Mach
    semantics to the concrete Mach semantics (file [Machabstr2mach]).
*)

Definition wt_regset (rs: regset) : Prop :=
  forall r, Val.has_type (rs r) (mreg_type r).

Definition wt_content (c: content) : Prop :=
  match c with
  | Datum32 v => Val.has_type v Tint
  | Datum64 v => Val.has_type v Tfloat
  | _ => True
  end.

Definition wt_frame (fr: frame) : Prop :=
  forall ofs, wt_content (fr.(contents) ofs).

Lemma wt_setreg:
  forall (rs: regset) (r: mreg) (v: val),
  Val.has_type v (mreg_type r) ->
  wt_regset rs -> wt_regset (rs#r <- v).
Proof.
  intros; red; intros. unfold Regmap.set. 
  case (RegEq.eq r0 r); intro.
  subst r0; assumption.
  apply H0.
Qed.

Lemma wt_get_slot:
  forall fr ty ofs v,
  get_slot fr ty ofs v ->
  wt_frame fr ->
  Val.has_type v ty. 
Proof.
  induction 1; intro. subst v. 
  set (pos := low fr + ofs).
  case ty; simpl.
  unfold getN. case (check_cont 3 (pos + 1) (contents fr)).
  generalize (H2 pos). unfold wt_content.
  destruct (contents fr pos); simpl; tauto.
  simpl; auto.
  unfold getN. case (check_cont 7 (pos + 1) (contents fr)).
  generalize (H2 pos). unfold wt_content.
  destruct (contents fr pos); simpl; tauto.
  simpl; auto.
Qed.

Lemma wt_set_slot:
  forall fr ty ofs v fr',
  set_slot fr ty ofs v fr' ->
  wt_frame fr ->
  Val.has_type v ty ->
  wt_frame fr'.
Proof.
  intros. induction H. 
  set (i := low fr + ofs).
  red; intro j; simpl. 
  assert (forall n ofs c,
            let c' := set_cont n ofs c in
            forall k, c' k = c k \/ c' k = Cont).
    induction n; simpl; intros.
    left; auto.
    unfold update. case (zeq k ofs0); intro.
    right; auto.
    apply IHn.
  destruct ty; simpl; unfold store_contents; unfold setN;
  unfold update; case (zeq j i); intro.
  red. assumption.
  elim (H 3%nat (i + 1) (contents fr) j); intro; rewrite H2.
  apply H0. red; auto. 
  red. assumption.
  elim (H 7%nat (i + 1) (contents fr) j); intro; rewrite H2.
  apply H0. red; auto. 
Qed.

Lemma wt_init_frame:
  forall f,
  wt_frame (init_frame f).
Proof.
  intros. unfold init_frame. 
  red; intros. simpl. exact I.
Qed.

Lemma incl_find_label:
  forall lbl c c', find_label lbl c = Some c' -> incl c' c.
Proof.
  induction c; simpl.
  intros; discriminate.
  case (is_label lbl a); intros.
  injection H; intro; subst c'; apply incl_tl; apply incl_refl.
  apply incl_tl; auto.
Qed.

Section SUBJECT_REDUCTION.

Variable p: program.
Hypothesis wt_p: wt_program p.
Let ge := Genv.globalenv p.

Definition exec_instr_prop 
  (f: function) (sp: val) (parent: frame)
  (c1: code) (rs1: regset) (fr1: frame) (m1: mem)
  (c2: code) (rs2: regset) (fr2: frame) (m2: mem) :=
    forall (WTF: wt_function f)
           (INCL: incl c1 f.(fn_code))
           (WTRS: wt_regset rs1)
           (WTFR: wt_frame fr1)
           (WTPA: wt_frame parent),
    incl c2 f.(fn_code) /\ wt_regset rs2 /\ wt_frame fr2.
Definition exec_function_body_prop
  (f: function) (parent: frame) (link ra: val)
  (rs1: regset) (m1: mem) (rs2: regset) (m2: mem) :=
    forall (WTF: wt_function f)
           (WTRS: wt_regset rs1)
           (WTPA: wt_frame parent)
           (WTLINK: Val.has_type link Tint)
           (WTRA: Val.has_type ra Tint),
    wt_regset rs2.
Definition exec_function_prop
  (f: function) (parent: frame)
  (rs1: regset) (m1: mem) (rs2: regset) (m2: mem) :=
    forall (WTF: wt_function f)
           (WTRS: wt_regset rs1)
           (WTPA: wt_frame parent),
    wt_regset rs2.

Lemma subject_reduction:
   (forall f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2,
      exec_instr ge f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2 ->
      exec_instr_prop f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2)
/\ (forall f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2,
      exec_instrs ge f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2 ->
      exec_instr_prop f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2)
/\ (forall f parent link ra rs1 m1 rs2 m2,
      exec_function_body ge f parent link ra rs1 m1 rs2 m2 ->
      exec_function_body_prop f parent link ra rs1 m1 rs2 m2)
/\ (forall f parent rs1 m1 rs2 m2,
      exec_function ge f parent rs1 m1 rs2 m2 ->
      exec_function_prop f parent rs1 m1 rs2 m2).
Proof.
  apply exec_mutual_induction; red; intros; 
  try (generalize (wt_function_instrs _ WTF _ (INCL _ (in_eq _ _))); intro;
       intuition eauto with coqlib).

  apply wt_setreg; auto. 
  inversion H0. rewrite H2. apply wt_get_slot with fr (Int.signed ofs); auto.

  inversion H0. eapply wt_set_slot; eauto. 
  rewrite <- H3. apply WTRS.

  inversion H0. apply wt_setreg; auto.
  rewrite H2. apply wt_get_slot with parent (Int.signed ofs); auto.

  apply wt_setreg; auto. inversion H0.
    simpl. subst args; subst op. simpl in H. 
    rewrite <- H2. replace v with (rs r1). apply WTRS. congruence.
    subst args; subst op. simpl in H. 
    replace v with Vundef. simpl; auto. congruence.
    replace (mreg_type res) with (snd (type_of_operation op)).
    apply type_of_operation_sound with function ge rs##args sp; auto.
    rewrite <- H6; reflexivity.

  apply wt_setreg; auto. inversion H1. rewrite H7.
  eapply type_of_chunk_correct; eauto.

  apply H1; auto.
  destruct ros; simpl in H. 
  apply (Genv.find_funct_prop wt_function wt_p H).
  destruct (Genv.find_symbol ge i). 
  apply (Genv.find_funct_ptr_prop wt_function wt_p H).
  discriminate.

  apply incl_find_label with lbl; auto. 
  apply incl_find_label with lbl; auto. 

  tauto.
  apply H0; auto.
  generalize (H0 WTF INCL WTRS WTFR WTPA). intros [A [B C]].
  apply H2; auto.

  assert (WTFR2: wt_frame fr2).
    eapply wt_set_slot; eauto. 
    eapply wt_set_slot; eauto.
    apply wt_init_frame.
  generalize (H3 WTF (incl_refl _) WTRS WTFR2 WTPA).
  tauto.

  apply (H0 Vzero Vzero). exact I. exact I. auto. auto. auto. 
  exact I. exact I.
Qed.

Lemma subject_reduction_instr:
   forall f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2,
      exec_instr ge f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2 ->
      exec_instr_prop f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2.
Proof (proj1 subject_reduction).

Lemma subject_reduction_instrs:
   forall f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2,
      exec_instrs ge f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2 ->
      exec_instr_prop f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2.
Proof (proj1 (proj2 subject_reduction)).

Lemma subject_reduction_function:
  forall f parent rs1 m1 rs2 m2,
      exec_function ge f parent rs1 m1 rs2 m2 ->
      exec_function_prop f parent rs1 m1 rs2 m2.
Proof (proj2 (proj2 (proj2 subject_reduction))).

End SUBJECT_REDUCTION.

(** * Preservation of the reserved frame slots during execution *)

(** We now show another result useful for the proof of implication
    between the two Mach semantics: well-typed functions do not
    change the values of the back link and return address fields
    of the frame slot (at offsets 0 and 4) during their execution.
    Actually, we show that the whole reserved part of the frame
    (between offsets 0 and 24) does not change. *)

Definition link_invariant (fr1 fr2: frame) : Prop :=
  forall pos v,
  0 <= pos < 20 ->
  get_slot fr1 Tint pos v -> get_slot fr2 Tint pos v.

Remark link_invariant_refl:
  forall fr, link_invariant fr fr.
Proof.
  intros; red; auto.
Qed.

Lemma set_slot_link_invariant:
  forall fr ty ofs v fr',
  set_slot fr ty ofs v fr' ->
  24 <= ofs ->
  link_invariant fr fr'.
Proof.
  induction 1. intros; red; intros.
  inversion H1. constructor. auto. exact H3. 
  simpl contents. simpl low. symmetry. rewrite H4. 
  apply load_store_contents_other. simpl. simpl in H3.
  omega.
Qed.

Lemma exec_instr_link_invariant:
  forall ge f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2,
  exec_instr ge f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2 ->
  wt_function f ->
  incl c1 f.(fn_code) ->
  incl c2 f.(fn_code) /\ link_invariant fr1 fr2.
Proof.
  induction 1; intros; 
  (split; [eauto with coqlib | try (apply link_invariant_refl)]).
  eapply set_slot_link_invariant; eauto.
  generalize (wt_function_instrs _ H0 _ (H1 _ (in_eq _ _))); intro.
  inversion H2. auto.
  eapply incl_find_label; eauto.
  eapply incl_find_label; eauto.
Qed.

Lemma exec_instrs_link_invariant:
  forall ge f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2,
  exec_instrs ge f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2 ->
  wt_function f ->
  incl c1 f.(fn_code) ->
  incl c2 f.(fn_code) /\ link_invariant fr1 fr2.
Proof.
  induction 1; intros.
  split. auto. apply link_invariant_refl.
  eapply exec_instr_link_invariant; eauto.
  generalize (IHexec_instrs1 H1 H2); intros [A B].
  generalize (IHexec_instrs2 H1 A); intros [C D].
  split. auto. red; auto.
Qed.


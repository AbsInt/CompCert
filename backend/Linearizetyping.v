(** Type preservation for the Linearize pass *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import Linear.
Require Import Linearize.
Require Import LTLtyping.
Require Import Lineartyping.
Require Import Conventions.

(** * Validity of resource bounds *)

(** In this section, we show that the resource bounds computed by
  [function_bounds] are valid: all references to callee-save registers
  and stack slots in the code of the function are within those bounds. *)

Section BOUNDS.

Variable f: Linear.function.
Let b := function_bounds f.

Lemma max_over_list_bound:
  forall (A: Set) (valu: A -> Z) (l: list A) (x: A),
  In x l -> valu x <= max_over_list A valu l.
Proof.
  intros until x. unfold max_over_list.
  assert (forall c z,
            let f := fold_left (fun x y => Zmax x (valu y)) c z in
            z <= f /\ (In x c -> valu x <= f)).
    induction c; simpl; intros.
    split. omega. tauto.
    elim (IHc (Zmax z (valu a))); intros. 
    split. apply Zle_trans with (Zmax z (valu a)). apply Zmax1. auto. 
    intro H1; elim H1; intro. 
    subst a. apply Zle_trans with (Zmax z (valu x)). 
    apply Zmax2. auto. auto.
  intro. elim (H l 0); intros. auto.
Qed.

Lemma max_over_instrs_bound:
  forall (valu: instruction -> Z) i,
  In i f.(fn_code) -> valu i <= max_over_instrs f valu.
Proof.
  intros. unfold max_over_instrs. apply max_over_list_bound; auto.
Qed.

Lemma max_over_regs_of_funct_bound:
  forall (valu: mreg -> Z) i r,
  In i f.(fn_code) -> In r (regs_of_instr i) ->
  valu r <= max_over_regs_of_funct f valu.
Proof.
  intros. unfold max_over_regs_of_funct. 
  apply Zle_trans with (max_over_regs_of_instr valu i).
  unfold max_over_regs_of_instr. apply max_over_list_bound. auto.
  apply max_over_instrs_bound. auto.
Qed.

Lemma max_over_slots_of_funct_bound:
  forall (valu: slot -> Z) i s,
  In i f.(fn_code) -> In s (slots_of_instr i) ->
  valu s <= max_over_slots_of_funct f valu.
Proof.
  intros. unfold max_over_slots_of_funct. 
  apply Zle_trans with (max_over_slots_of_instr valu i).
  unfold max_over_slots_of_instr. apply max_over_list_bound. auto.
  apply max_over_instrs_bound. auto.
Qed.

Lemma int_callee_save_bound:
  forall i r,
  In i f.(fn_code) -> In r (regs_of_instr i) ->
  index_int_callee_save r < bound_int_callee_save b.
Proof.
  intros. apply Zlt_le_trans with (int_callee_save r).
  unfold int_callee_save. omega.
  unfold b, function_bounds, bound_int_callee_save. 
  eapply max_over_regs_of_funct_bound; eauto.
Qed.

Lemma float_callee_save_bound:
  forall i r,
  In i f.(fn_code) -> In r (regs_of_instr i) ->
  index_float_callee_save r < bound_float_callee_save b.
Proof.
  intros. apply Zlt_le_trans with (float_callee_save r).
  unfold float_callee_save. omega.
  unfold b, function_bounds, bound_float_callee_save. 
  eapply max_over_regs_of_funct_bound; eauto.
Qed.

Lemma int_local_slot_bound:
  forall i ofs,
  In i f.(fn_code) -> In (Local ofs Tint) (slots_of_instr i) ->
  ofs < bound_int_local b.
Proof.
  intros. apply Zlt_le_trans with (int_local (Local ofs Tint)).
  unfold int_local. omega.
  unfold b, function_bounds, bound_int_local.
  eapply max_over_slots_of_funct_bound; eauto.
Qed.

Lemma float_local_slot_bound:
  forall i ofs,
  In i f.(fn_code) -> In (Local ofs Tfloat) (slots_of_instr i) ->
  ofs < bound_float_local b.
Proof.
  intros. apply Zlt_le_trans with (float_local (Local ofs Tfloat)).
  unfold float_local. omega.
  unfold b, function_bounds, bound_float_local.
  eapply max_over_slots_of_funct_bound; eauto.
Qed.

Lemma outgoing_slot_bound:
  forall i ofs ty,
  In i f.(fn_code) -> In (Outgoing ofs ty) (slots_of_instr i) ->
  ofs + typesize ty <= bound_outgoing b.
Proof.
  intros. change (ofs + typesize ty) with (outgoing_slot (Outgoing ofs ty)).
  unfold b, function_bounds, bound_outgoing.
  apply Zmax_bound_r. apply Zmax_bound_r. 
  eapply max_over_slots_of_funct_bound; eauto.
Qed.

Lemma size_arguments_bound:
  forall sig ros,
  In (Lcall sig ros) f.(fn_code) ->
  size_arguments sig <= bound_outgoing b.
Proof.
  intros. change (size_arguments sig) with (outgoing_space (Lcall sig ros)).
  unfold b, function_bounds, bound_outgoing.
  apply Zmax_bound_r. apply Zmax_bound_l.
  apply max_over_instrs_bound; auto.
Qed.

End BOUNDS.

(** Consequently, all machine registers or stack slots mentioned by one
  of the instructions of function [f] are within bounds. *)

Lemma mreg_is_bounded:
  forall f i r,
  In i f.(fn_code) -> In r (regs_of_instr i) ->
  mreg_bounded f r.
Proof.
  intros. unfold mreg_bounded. 
  case (mreg_type r).
  eapply int_callee_save_bound; eauto.
  eapply float_callee_save_bound; eauto.
Qed.

Lemma slot_is_bounded:
  forall f i s,
  In i (transf_function f).(fn_code) -> In s (slots_of_instr i) ->
  LTLtyping.slot_bounded f s ->
  slot_bounded (transf_function f) s.
Proof.
  intros. unfold slot_bounded. 
  destruct s.
  destruct t.
  split. exact H1. eapply int_local_slot_bound; eauto.
  split. exact H1. eapply float_local_slot_bound; eauto.
  unfold linearize_function; simpl. exact H1.
  split. exact H1. eapply outgoing_slot_bound; eauto.
Qed.

(** * Conservation property of the cleanup pass *)

(** We show that the cleanup pass only deletes some [Lgoto] instructions:
  all other instructions present in the output of naive linearization
  are in the cleaned-up code, and all instructions in the cleaned-up code
  are in the output of naive linearization. *)

Lemma cleanup_code_conservation:
  forall i,
  match i with Lgoto _ => False | _ => True end ->
  forall c,
  In i c -> In i (cleanup_code c).
Proof.
  induction c; simpl.
  auto.
  intro.
  assert (In i (a :: cleanup_code c)).
    elim H0; intro. subst i. auto with coqlib.
    apply in_cons. auto.
  destruct a; auto. 
  assert (In i (cleanup_code c)).
    elim H1; intro. subst i. contradiction. auto.
  case (starts_with l c). auto. apply in_cons; auto. 
Qed.

Lemma cleanup_function_conservation:
  forall f i,
  In i (linearize_function f).(fn_code) ->
  match i with Lgoto _ => False | _ => True end ->
  In i (transf_function f).(fn_code).
Proof.
  intros. unfold transf_function. unfold cleanup_function.
  simpl. simpl in H0. eapply cleanup_code_conservation; eauto.
Qed.

Lemma cleanup_code_conservation_2:
  forall i c, In i (cleanup_code c) -> In i c.
Proof.
  induction c; simpl.
  auto.
  assert (In i (a :: cleanup_code c) -> a = i \/ In i c).
    intro. elim H; tauto.
  destruct a; auto.
  case (starts_with l c). auto. auto. 
Qed.

Lemma cleanup_function_conservation_2:
  forall f i,
  In i (transf_function f).(fn_code) ->
  In i (linearize_function f).(fn_code).
Proof.
  simpl. intros. eapply cleanup_code_conservation_2; eauto.
Qed.

(** * Type preservation for the linearization pass *)

Lemma linearize_block_incl:
  forall k b, incl k (linearize_block b k).
Proof.
  induction b; simpl; auto with coqlib.
  case (starts_with n k); auto with coqlib.
Qed.

Lemma wt_linearize_block:
  forall f k,
  (forall i, In i k -> wt_instr (transf_function f) i) ->
  forall b i,
  wt_block f b ->
  incl (linearize_block b k) (linearize_function f).(fn_code) ->
  In i (linearize_block b k) -> wt_instr (transf_function f) i.
Proof.
  induction b; simpl; intros;
  try (generalize (cleanup_function_conservation 
                     _ _ (H1 _ (in_eq _ _)) I));
  inversion H0;
  try (elim H2; intro; [subst i|eauto with coqlib]);
  intros.
  (* getstack *)
  constructor. auto. eapply slot_is_bounded; eauto.
  simpl; auto with coqlib. 
  eapply mreg_is_bounded; eauto.
  simpl; auto with coqlib. 
  (* setstack *)
  constructor. auto. auto. 
  eapply slot_is_bounded; eauto. 
  simpl; auto with coqlib. 
  (* move *)
  subst o; subst l. constructor. auto. 
  eapply mreg_is_bounded; eauto.
  simpl; auto with coqlib. 
  (* undef *)
  subst o; subst l. constructor. 
  eapply mreg_is_bounded; eauto.
  simpl; auto with coqlib. 
  (* other ops *)
  constructor; auto. 
  eapply mreg_is_bounded; eauto.
  simpl; auto with coqlib. 
  (* load *)
  constructor; auto.
  eapply mreg_is_bounded; eauto.
  simpl; auto with coqlib. 
  (* store *)
  constructor; auto.
  (* call *)
  constructor; auto. 
  eapply size_arguments_bound; eauto.
  (* goto *)
  constructor. 
  (* cond *)
  destruct (starts_with n k).
  elim H2; intro.
  subst i. constructor. 
  rewrite H4. destruct c; reflexivity.
  elim H8; intro.
  subst i. constructor.
  eauto with coqlib.
  elim H2; intro.
  subst i. constructor. auto.
  elim H8; intro.
  subst i. constructor.
  eauto with coqlib.
  (* return *)
  constructor.
Qed.

Lemma wt_linearize_body:
  forall f,
  LTLtyping.wt_function f ->
  forall enum i,
  incl (linearize_body f enum) (linearize_function f).(fn_code) ->
  In i (linearize_body f enum) -> wt_instr (transf_function f) i.
Proof.
  induction enum.
  simpl; intros; contradiction.
  intro i. simpl.
  caseEq (LTL.fn_code f)!a. intros b EQ INCL IN.
  elim IN; intro. subst i; constructor. 
  apply wt_linearize_block with (linearize_body f enum) b.
  intros; apply IHenum. 
  apply incl_tran with (linearize_block b (linearize_body f enum)).
  apply linearize_block_incl.
  eauto with coqlib.
  auto.
  eapply H; eauto.
  eauto with coqlib. auto.
  auto.
Qed. 

Lemma wt_transf_function:
  forall f,
  LTLtyping.wt_function f ->
  wt_function (transf_function f). 
Proof.
  intros; red; intros.
  apply wt_linearize_body with (enumerate f); auto.
  simpl. apply incl_refl.
  apply cleanup_function_conservation_2; auto.
Qed.

Lemma program_typing_preserved:
  forall (p: LTL.program),
  LTLtyping.wt_program p ->
  Lineartyping.wt_program (transf_program p).
Proof.
  intros; red; intros.
  generalize (transform_program_function transf_function p i f H0).
  intros [f0 [IN TR]].
  subst f. apply wt_transf_function; auto. 
  apply (H i f0 IN).
Qed.

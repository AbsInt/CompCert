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

(** Type system for the Mach intermediate language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Memory.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Conventions.
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
     mreg_type r = ty ->
     wt_instr (Msetstack r ofs ty)
  | wt_Mgetparam:
     forall ofs ty r,
     mreg_type r = ty ->
     wt_instr (Mgetparam ofs ty r)
  | wt_Mopmove:
     forall r1 r,
     mreg_type r1 = mreg_type r ->
     wt_instr (Mop Omove (r1 :: nil) r)
  | wt_Mop:
     forall op args res,
      op <> Omove ->
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
  | wt_Mtailcall:
      forall sig ros,
      tailcall_possible sig ->
      match ros with inl r => mreg_type r = Tint | inr s => True end ->
      wt_instr (Mtailcall sig ros)
  | wt_Mbuiltin:
     forall ef args res,
      List.map mreg_type args = (ef_sig ef).(sig_args) ->
      mreg_type res = proj_sig_res (ef_sig ef) ->
      wt_instr (Mbuiltin ef args res)
  | wt_Mgoto:
      forall lbl,
      wt_instr (Mgoto lbl)
  | wt_Mcond:
      forall cond args lbl,
      List.map mreg_type args = type_of_condition cond ->
      wt_instr (Mcond cond args lbl)
  | wt_Mjumptable:
      forall arg tbl,
      mreg_type arg = Tint ->
      list_length_z tbl * 4 <= Int.max_signed ->
      wt_instr (Mjumptable arg tbl)
  | wt_Mreturn: 
      wt_instr Mreturn.

Record wt_function (f: function) : Prop := mk_wt_function {
  wt_function_instrs:
    forall instr, In instr f.(fn_code) -> wt_instr instr;
  wt_function_stacksize:
    f.(fn_stacksize) >= 0;
  wt_function_framesize:
    0 <= f.(fn_framesize) <= -Int.min_signed;
  wt_function_framesize_aligned:
    (4 | f.(fn_framesize));
  wt_function_link:
    0 <= Int.signed f.(fn_link_ofs)
    /\ Int.signed f.(fn_link_ofs) + 4 <= f.(fn_framesize);
  wt_function_link_aligned:
    (4 | Int.signed f.(fn_link_ofs));
  wt_function_retaddr:
    0 <= Int.signed f.(fn_retaddr_ofs)
    /\ Int.signed f.(fn_retaddr_ofs) + 4 <= f.(fn_framesize);
  wt_function_retaddr_aligned:
    (4 | Int.signed f.(fn_retaddr_ofs));
  wt_function_link_retaddr:
    Int.signed f.(fn_retaddr_ofs) + 4 <= Int.signed f.(fn_link_ofs)
    \/ Int.signed f.(fn_link_ofs) + 4 <= Int.signed f.(fn_retaddr_ofs)
}.

Inductive wt_fundef: fundef -> Prop :=
  | wt_fundef_external: forall ef,
      wt_fundef (External ef)
  | wt_function_internal: forall f,
      wt_function f ->
      wt_fundef (Internal f).

Definition wt_program (p: program) : Prop :=
  forall i f, In (i, f) (prog_funct p) -> wt_fundef f.

(** * Type soundness *)

Require Import Machabstr.

(** We show a weak type soundness result for the abstract semantics
    of Mach: for a well-typed Mach program, if a transition is taken
    from a state where registers hold values of their static types,
    registers in the final state hold values of their static types
    as well.  This is a subject reduction theorem for our type system.
    It is used in the proof of implication from the abstract Mach
    semantics to the concrete Mach semantics (file [Machabstr2concr]).
*)

Definition wt_regset (rs: regset) : Prop :=
  forall r, Val.has_type (rs r) (mreg_type r).

Definition wt_frame (fr: frame) : Prop :=
  forall ty ofs, Val.has_type (fr ty ofs) ty.

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

Lemma wt_undef_temps:
  forall rs, wt_regset rs -> wt_regset (undef_temps rs).
Proof.
  unfold undef_temps. 
  generalize (int_temporaries ++ float_temporaries).
  induction l; simpl; intros. auto.
  apply IHl. red; intros. unfold Regmap.set.
  destruct (RegEq.eq r a). constructor. auto. 
Qed.

Lemma wt_undef_op:
  forall op rs, wt_regset rs -> wt_regset (undef_op op rs).
Proof.
  intros. set (W := wt_undef_temps rs H). 
  destruct op; simpl; auto.
Qed.

Lemma wt_undef_getparam:
  forall rs, wt_regset rs -> wt_regset (rs#IT1 <- Vundef).
Proof.
  intros; red; intros. unfold Regmap.set. 
  destruct (RegEq.eq r IT1). constructor. auto.
Qed.

Lemma wt_get_slot:
  forall f fr ty ofs v,
  get_slot f fr ty ofs v ->
  wt_frame fr ->
  Val.has_type v ty. 
Proof.
  induction 1; intros.
  subst v. apply H1.
Qed.

Lemma wt_set_slot:
  forall f fr ty ofs v fr',
  set_slot f fr ty ofs v fr' ->
  wt_frame fr ->
  Val.has_type v ty ->
  wt_frame fr'.
Proof.
  intros. induction H. subst fr'; red; intros. unfold update.
  destruct (zeq (ofs - f.(fn_framesize)) ofs0).
  destruct (typ_eq ty ty0). congruence. exact I.
  destruct (zle (ofs0 + AST.typesize ty0) (ofs - f.(fn_framesize))).
  apply H0.
  destruct (zle (ofs - f.(fn_framesize) + AST.typesize ty) ofs0).
  apply H0.
  exact I.
Qed.

Lemma wt_empty_frame:
  wt_frame empty_frame.
Proof.
  intros; red; intros; exact I.
Qed.

Lemma is_tail_find_label:
  forall lbl c c', find_label lbl c = Some c' -> is_tail c' c.
Proof.
  induction c; simpl.
  intros; discriminate.
  case (is_label lbl a); intros.
  injection H; intro; subst c'. constructor. constructor.
  constructor; auto.
Qed.

Section SUBJECT_REDUCTION.

Inductive wt_stackframe: stackframe -> Prop :=
  | wt_stackframe_intro: forall f sp c fr,
      wt_function f ->
      Val.has_type sp Tint ->
      is_tail c f.(fn_code) ->
      wt_frame fr ->
      wt_stackframe (Stackframe f sp c fr).

Inductive wt_state: state -> Prop :=
  | wt_state_intro: forall stk f sp c rs fr m
      (STK: forall s, In s stk -> wt_stackframe s)
      (WTF: wt_function f)
      (WTSP: Val.has_type sp Tint)
      (TAIL: is_tail c f.(fn_code))
      (WTRS: wt_regset rs)
      (WTFR: wt_frame fr),
      wt_state (State stk f sp c rs fr m)
  | wt_state_call: forall stk f rs m,
      (forall s, In s stk -> wt_stackframe s) ->
      wt_fundef f ->
      wt_regset rs ->
      wt_state (Callstate stk f rs m)
  | wt_state_return: forall stk rs m,
      (forall s, In s stk -> wt_stackframe s) ->
      wt_regset rs ->
      wt_state (Returnstate stk rs m).

Variable p: program.
Hypothesis wt_p: wt_program p.
Let ge := Genv.globalenv p.

Lemma subject_reduction:
  forall s1 t s2, step ge s1 t s2 ->
  forall (WTS: wt_state s1), wt_state s2.
Proof.
  induction 1; intros; inv WTS;
  try (generalize (wt_function_instrs _ WTF _ (is_tail_in TAIL)); intro WTI;
       eapply wt_state_intro; eauto with coqlib).

  apply wt_setreg; auto. inv WTI. eapply wt_get_slot; eauto.

  eapply wt_set_slot; eauto. inv WTI; auto. 

  assert (mreg_type dst = ty).
    inv WTI; auto.
  assert (wt_frame (parent_frame s)).
    destruct s; simpl. apply wt_empty_frame. 
    generalize (STK s (in_eq _ _)); intro. inv H1. auto. 
  apply wt_setreg; auto.
  rewrite H0. eapply wt_get_slot; eauto.
  apply wt_undef_getparam; auto.

(* op *)
  apply wt_setreg; auto.
  inv WTI.
  (* move *)
  simpl in H. inv H. rewrite <- H1. apply WTRS.
  (* not move *)
  replace (mreg_type res) with (snd (type_of_operation op)).
  apply type_of_operation_sound with fundef unit ge rs##args sp; auto.
  rewrite <- H4; reflexivity.
  apply wt_undef_op; auto.

(* load *)
  apply wt_setreg; auto. inv WTI. rewrite H6. eapply type_of_chunk_correct; eauto.
  apply wt_undef_temps; auto.

(* store *)
  apply wt_undef_temps; auto.

(* call *)
  assert (WTFD: wt_fundef f').
    destruct ros; simpl in H.
    apply (Genv.find_funct_prop wt_fundef _ _ wt_p H).
    destruct (Genv.find_symbol ge i); try discriminate.
    apply (Genv.find_funct_ptr_prop wt_fundef _ _ wt_p H).
  econstructor; eauto.
  intros. elim H0; intro. subst s0. econstructor; eauto with coqlib.
  auto.

(* tailcall *)
  assert (WTFD: wt_fundef f').
    destruct ros; simpl in H.
    apply (Genv.find_funct_prop wt_fundef _ _ wt_p H).
    destruct (Genv.find_symbol ge i); try discriminate.
    apply (Genv.find_funct_ptr_prop wt_fundef _ _ wt_p H).
  econstructor; eauto.

(* extcall *)
  apply wt_setreg; auto. 
  inv WTI. rewrite H4. eapply external_call_well_typed; eauto.
  apply wt_undef_temps; auto.

(* goto *)  
  apply is_tail_find_label with lbl; congruence.
(* cond *)
  apply is_tail_find_label with lbl; congruence. apply wt_undef_temps; auto.
  apply wt_undef_temps; auto.
(* jumptable *)
  apply is_tail_find_label with lbl; congruence. apply wt_undef_temps; auto. 

(* return *)
  econstructor; eauto.

(* internal function *)
  econstructor; eauto with coqlib. inv H5; auto. exact I. 
  apply wt_empty_frame.

(* external function *)
  econstructor; eauto. apply wt_setreg; auto.
  generalize (external_call_well_typed _ _ _ _ _ _ _ H).  
  unfold proj_sig_res, loc_result.
  destruct (sig_res (ef_sig ef)).
  destruct t0; simpl; auto.
  simpl; auto.

(* returnstate *)
  generalize (H1 _ (in_eq _ _)); intro. inv H.
  econstructor; eauto. 
  eauto with coqlib.
Qed.

End SUBJECT_REDUCTION.


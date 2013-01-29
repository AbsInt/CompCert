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

(** Correctness proof for the [RRE] pass. *)

Require Import Axioms.
Require Import Coqlib.
Require Import AST.
Require Import Values.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Import Linear.
Require Import RRE.

(** * Operations over equations *)

Lemma find_reg_containing_sound:
  forall s r eqs, find_reg_containing s eqs = Some r -> In (mkeq r s) eqs.
Proof.
  induction eqs; simpl; intros.
  congruence.
  destruct (slot_eq (e_slot a) s). inv H. left; destruct a; auto. right; eauto.
Qed.

Definition equations_hold (ls: locset) (eqs: equations) : Prop :=
  forall e, In e eqs -> ls (S (e_slot e)) = ls (R (e_reg e)).

Lemma nil_hold:
  forall ls, equations_hold ls nil.
Proof.
  red; intros; contradiction.
Qed.

Lemma In_kill_loc:
  forall e l eqs,
  In e (kill_loc l eqs) ->
  In e eqs /\ Loc.diff (S (e_slot e)) l /\ Loc.diff (R (e_reg e)) l.
Proof.
  induction eqs; simpl kill_loc; simpl In; intros.
  tauto.
  destruct (Loc.diff_dec (S (e_slot a)) l).
  destruct (Loc.diff_dec (R (e_reg a)) l).
  simpl in H.  intuition congruence. 
  simpl in H.  intuition.
  simpl in H.  intuition.
Qed.

Lemma kill_loc_hold:
  forall ls eqs l v,
  equations_hold ls eqs ->
  equations_hold (Locmap.set l v ls) (kill_loc l eqs).
Proof.
  intros; red; intros. 
  exploit In_kill_loc; eauto. intros [A [B C]].
  repeat rewrite Locmap.gso; auto; apply Loc.diff_sym; auto.
Qed.

Lemma In_kill_locs:
  forall e ll eqs,
  In e (kill_locs ll eqs) ->
  In e eqs /\ Loc.notin (S (e_slot e)) ll /\ Loc.notin (R (e_reg e)) ll.
Proof.
Opaque Loc.diff.
  induction ll; simpl; intros.
  tauto.
  exploit IHll; eauto. intros [A [B C]]. exploit In_kill_loc; eauto. intros [D [E F]]. 
  tauto.
Qed.

Lemma kill_locs_hold:
  forall ll ls eqs,
  equations_hold ls eqs ->
  equations_hold (Locmap.undef ll ls) (kill_locs ll eqs).
Proof.
  intros; red; intros. exploit In_kill_locs; eauto. intros [A [B C]]. 
  repeat rewrite Locmap.guo; auto. 
Qed.

Lemma kill_temps_hold:
  forall ls eqs,
  equations_hold ls eqs ->
  equations_hold (LTL.undef_temps ls) (kill_temps eqs).
Proof.
  exact (kill_locs_hold temporaries).
Qed.

Lemma kill_at_move_hold:
  forall ls eqs,
  equations_hold ls eqs ->
  equations_hold (undef_setstack ls) (kill_at_move eqs).
Proof.
  exact (kill_locs_hold destroyed_at_move).
Qed.

Lemma kill_at_op_hold:
  forall op ls eqs,
  equations_hold ls eqs ->
  equations_hold (undef_op op ls) (kill_op op eqs).
Proof.
  intros op. 
  destruct op; exact kill_temps_hold || exact kill_at_move_hold.
Qed.

Lemma eqs_getstack_hold:
  forall rs r s eqs,
  equations_hold rs eqs ->
  equations_hold (Locmap.set (R r) (rs (S s)) rs)
                 (mkeq r s :: kill_loc (R r) eqs).
Proof.
Transparent Loc.diff.
  intros; red; intros. simpl in H0; destruct H0.
  subst e. simpl. rewrite Locmap.gss; rewrite Locmap.gso; auto. red; auto.
  exploit In_kill_loc; eauto. intros [D [E F]].
  repeat rewrite Locmap.gso. auto. 
  apply Loc.diff_sym; auto. apply Loc.diff_sym; auto.
Qed.

Lemma eqs_movestack_hold:
  forall rs r s eqs,
  equations_hold rs eqs ->
  equations_hold (Locmap.set (R r) (rs (S s)) (undef_setstack rs))
                 (kill_at_move (mkeq r s :: kill_loc (R r) eqs)).
Proof.
  unfold undef_setstack, kill_at_move; intros; red; intros.
  exploit In_kill_locs; eauto. intros [A [B C]].
  simpl in A; destruct A.
  subst e. rewrite Locmap.gss. rewrite Locmap.gso. apply Locmap.guo. auto. 
  simpl; auto.
  exploit In_kill_loc; eauto. intros [D [E F]].
  repeat rewrite Locmap.gso. repeat rewrite Locmap.guo; auto.
  apply Loc.diff_sym; auto. apply Loc.diff_sym; auto.
Qed.

Lemma eqs_setstack_hold:
  forall rs r s eqs,
  equations_hold rs eqs ->
  equations_hold (Locmap.set (S s) (rs (R r)) (undef_setstack rs))
                 (kill_at_move (mkeq r s :: kill_loc (S s) eqs)).
Proof.
  unfold undef_setstack, kill_at_move; intros; red; intros.
  exploit In_kill_locs; eauto. intros [A [B C]].
  simpl in A; destruct A.
  subst e. rewrite Locmap.gss. rewrite Locmap.gso. rewrite Locmap.guo. auto. 
  auto. simpl. destruct s; auto.
  exploit In_kill_loc; eauto. intros [D [E F]].
  repeat rewrite Locmap.gso. repeat rewrite Locmap.guo; auto.
  apply Loc.diff_sym; auto. apply Loc.diff_sym; auto.
Qed.

Lemma locmap_set_reg_same:
  forall rs r,
  Locmap.set (R r) (rs (R r)) rs = rs.
Proof.
  intros. apply extensionality; intros. 
  destruct (Loc.eq x (R r)).
  subst x. apply Locmap.gss.
  apply Locmap.gso. apply Loc.diff_reg_right; auto.
Qed.

(** * Agreement between values of locations *)

(** Values of locations may differ between the original and transformed
  program: after a [Lgetstack] is optimized to a [Lop Omove], 
  the values of [destroyed_at_move] temporaries differ.  This
  can only happen in parts of the code where the [safe_move_insertion]
  function returns [true].  *)

Definition agree (sm: bool) (rs rs': locset) : Prop :=
  forall l, sm = false \/ Loc.notin l destroyed_at_move -> rs' l = rs l.

Lemma agree_false:
  forall rs rs',
  agree false rs rs' <-> rs' = rs.
Proof.
  intros; split; intros.
  apply extensionality; intros. auto.
  subst rs'. red; auto. 
Qed.

Lemma agree_slot:
  forall sm rs rs' s,
  agree sm rs rs' -> rs' (S s) = rs (S s).
Proof.
Transparent Loc.diff.
  intros. apply H. right. simpl; destruct s; tauto.
Qed.

Lemma agree_reg:
  forall sm rs rs' r,
  agree sm rs rs' ->
  sm = false \/ ~In r destroyed_at_move_regs -> rs' (R r) = rs (R r).
Proof.
  intros. apply H. destruct H0; auto. right. 
  simpl in H0; simpl; intuition congruence.
Qed.

Lemma agree_regs:
  forall sm rs rs' rl,
  agree sm rs rs' ->
  sm = false \/ list_disjoint rl destroyed_at_move_regs -> reglist rs' rl = reglist rs rl.
Proof.
  induction rl; intros; simpl. 
  auto.
  decEq. apply agree_reg with sm. auto.
    destruct H0. auto. right. eapply list_disjoint_notin; eauto with coqlib.
  apply IHrl; auto. destruct H0; auto. right. eapply list_disjoint_cons_left; eauto.
Qed.

Lemma agree_set:
  forall sm rs rs' l v,
  agree sm rs rs' ->
  agree sm (Locmap.set l v rs) (Locmap.set l v rs').
Proof.
  intros; red; intros.
  unfold Locmap.set. 
  destruct (Loc.eq l l0). auto. 
  destruct (Loc.overlap l l0). auto.
  apply H; auto.
Qed. 

Lemma agree_undef_move_1:
  forall sm rs rs',
  agree sm rs rs' ->
  agree true rs (undef_setstack rs').
Proof.
  intros. unfold undef_setstack. red; intros.
  destruct H0. congruence. rewrite Locmap.guo; auto.
Qed.

Remark locmap_undef_equal:
  forall x ll rs rs',
  (forall l, Loc.notin l ll -> rs' l = rs l) ->
  Locmap.undef ll rs' x = Locmap.undef ll rs x.
Proof.
  induction ll; intros; simpl.
  apply H. simpl. auto.
  apply IHll. intros. unfold Locmap.set. 
  destruct (Loc.eq a l). auto. destruct (Loc.overlap a l) eqn:?. auto. 
  apply H. simpl. split; auto. apply Loc.diff_sym. apply Loc.non_overlap_diff; auto.
Qed. 

Lemma agree_undef_move_2:
  forall sm rs rs',
  agree sm rs rs' ->
  agree false (undef_setstack rs) (undef_setstack rs').
Proof.
  intros. rewrite agree_false.
  apply extensionality; intros. unfold undef_setstack. apply locmap_undef_equal. auto.
Qed.

Lemma agree_undef_temps:
  forall sm rs rs',
  agree sm rs rs' ->
  agree false (LTL.undef_temps rs) (LTL.undef_temps rs').
Proof.
  intros. rewrite agree_false.
  apply extensionality; intros. unfold LTL.undef_temps. apply locmap_undef_equal.
  intros. apply H. right. simpl in H0; simpl; tauto.
Qed.

Lemma agree_undef_op:
  forall op sm rs rs',
  agree sm rs rs' ->
  agree false (undef_op op rs) (undef_op op rs').
Proof.
  intros op.
  destruct op; exact agree_undef_temps || exact agree_undef_move_2.
Qed.

Lemma transl_find_label:
  forall lbl c eqs,
  find_label lbl (transf_code eqs c) =
  option_map (transf_code nil) (find_label lbl c).
Proof.
  induction c; simpl; intros.
  auto.
  destruct a; simpl; auto.
  destruct (is_incoming s); simpl; auto.
  destruct (contains_equation s m eqs); auto.
  destruct (find_reg_containing s eqs); simpl; auto.
  destruct (safe_move_insertion c); simpl; auto. 
  destruct (peq lbl l); simpl; auto.
Qed.

(** * Semantic preservation *)

Section PRESERVATION.

Variable prog: program.
Let tprog := transf_program prog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof (@Genv.find_funct_transf _ _ _ transf_fundef prog).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof (@Genv.find_funct_ptr_transf _ _ _ transf_fundef prog).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (@Genv.find_symbol_transf _ _ _ transf_fundef prog).

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof (@Genv.find_var_info_transf _ _ _ transf_fundef prog).

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; reflexivity.
Qed.

Lemma find_function_translated:
  forall ros rs fd,
  find_function ge ros rs = Some fd ->
  find_function tge ros rs = Some (transf_fundef fd).
Proof.
  intros. destruct ros; simpl in *. 
  apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i). 
  apply function_ptr_translated; auto. 
  congruence.
Qed.

Inductive match_frames: stackframe -> stackframe -> Prop :=
  | match_frames_intro:
      forall f sp rs c,
      match_frames (Stackframe f sp rs c)
                   (Stackframe (transf_function f) sp rs (transf_code nil c)).

Inductive match_states: state -> state -> Prop :=
  | match_states_regular:
      forall sm stk f sp c rs m stk' rs' eqs
        (STK: list_forall2 match_frames stk stk')
        (EQH: equations_hold rs' eqs)
        (AG: agree sm rs rs')
        (SAFE: sm = false \/ safe_move_insertion c = true),
      match_states (State stk f sp c rs m)
                   (State stk' (transf_function f) sp (transf_code eqs c) rs' m)
  | match_states_call:
      forall stk f rs m stk'
        (STK: list_forall2 match_frames stk stk'),
      match_states (Callstate stk f rs m)
                   (Callstate stk' (transf_fundef f) rs m)
  | match_states_return:
      forall stk rs m stk'
        (STK: list_forall2 match_frames stk stk'),
      match_states (Returnstate stk rs m)
                   (Returnstate stk' rs m).

Definition measure (S: state) : nat :=
  match S with
  | State s f sp c rs m => List.length c
  | _ => 0%nat
  end.

Remark match_parent_locset:
  forall stk stk',
  list_forall2 match_frames stk stk' ->
  return_regs (parent_locset stk') = return_regs (parent_locset stk).
Proof.
  intros. inv H; auto. inv H0; auto.
Qed.

Theorem transf_step_correct:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
Opaque destroyed_at_move_regs.
  induction 1; intros; inv MS; simpl.
(** getstack *)
  simpl in SAFE. 
  assert (SAFE': sm = false \/ ~In r destroyed_at_move_regs /\ safe_move_insertion b = true).
    destruct (in_dec mreg_eq r destroyed_at_move_regs); simpl in SAFE; intuition congruence. 
  destruct (is_incoming sl) eqn:?.
  (* incoming, stays as getstack *)
  assert (UGS: forall rs, undef_getstack sl rs = Locmap.set (R IT1) Vundef rs).
    destruct sl; simpl in Heqb0; discriminate || auto.
  left; econstructor; split. constructor.
  repeat rewrite UGS.
  apply match_states_regular with sm. auto.
  apply kill_loc_hold. apply kill_loc_hold; auto.
  rewrite (agree_slot _ _ _ sl AG). apply agree_set. apply agree_set. auto.
  tauto.
  (* not incoming *)
  assert (UGS: forall rs, undef_getstack sl rs = rs). 
    destruct sl; simpl in Heqb0; discriminate || auto.
  unfold contains_equation. 
  destruct (in_dec eq_equation (mkeq r sl) eqs); simpl.
  (* eliminated *)
  right.  split. omega. split. auto. rewrite UGS.  
  exploit EQH; eauto. simpl. intro EQ.
  assert (EQ1: rs' (S sl) = rs (S sl)) by (eapply agree_slot; eauto).
  assert (EQ2: rs' (R r) = rs (R r)) by (eapply agree_reg; eauto; tauto).
  rewrite <- EQ1; rewrite EQ; rewrite EQ2. rewrite locmap_set_reg_same.
  apply match_states_regular with sm; auto; tauto. 
  (* found an equation *)
  destruct (find_reg_containing sl eqs) as [r'|] eqn:?.
  exploit EQH. eapply find_reg_containing_sound; eauto. 
  simpl; intro EQ.
  (* turned into a move *)
  destruct (safe_move_insertion b) eqn:?. 
  left; econstructor; split. constructor. simpl; eauto. 
  rewrite UGS. rewrite <- EQ.
  apply match_states_regular with true; auto. 
  apply eqs_movestack_hold; auto. 
  rewrite (agree_slot _ _ _ sl AG). apply agree_set. eapply agree_undef_move_1; eauto.
  (* left as a getstack *)
  left; econstructor; split. constructor.
  repeat rewrite UGS.
  apply match_states_regular with sm. auto. 
  apply eqs_getstack_hold; auto. 
  rewrite (agree_slot _ _ _ sl AG). apply agree_set. auto. 
  intuition congruence. 
  (* no equation, left as a getstack *)
  left; econstructor; split. constructor.
  repeat rewrite UGS.
  apply match_states_regular with sm. auto. 
  apply eqs_getstack_hold; auto. 
  rewrite (agree_slot _ _ _ sl AG). apply agree_set. auto.
  tauto.

(* setstack *)
  left; econstructor; split. constructor.
  apply match_states_regular with false; auto.
  apply eqs_setstack_hold; auto.
  rewrite (agree_reg _ _ _ r AG). apply agree_set. eapply agree_undef_move_2; eauto. 
  simpl in SAFE. destruct (in_dec mreg_eq r destroyed_at_move_regs); simpl in SAFE; intuition congruence.

(* op *)
  left; econstructor; split. constructor. 
  instantiate (1 := v). rewrite <- H.
  rewrite (agree_regs _ _ _ args AG). 
  apply eval_operation_preserved. exact symbols_preserved.
  simpl in SAFE. destruct (list_disjoint_dec mreg_eq args destroyed_at_move_regs); simpl in SAFE; intuition congruence.
  apply match_states_regular with false; auto.
  apply kill_loc_hold; apply kill_at_op_hold; auto.
  apply agree_set. eapply agree_undef_op; eauto.

(* load *)
  left; econstructor; split.
  econstructor.  instantiate (1 := a).  rewrite <- H.
  rewrite (agree_regs _ _ _ args AG). 
  apply eval_addressing_preserved.  exact symbols_preserved.
  simpl in SAFE. destruct (list_disjoint_dec mreg_eq args destroyed_at_move_regs); simpl in SAFE; intuition congruence.
  eauto.
  apply match_states_regular with false; auto.
  apply kill_loc_hold; apply kill_temps_hold; auto.
  apply agree_set. eapply agree_undef_temps; eauto.

(* store *)
Opaque list_disjoint_dec.
  simpl in SAFE.
  assert (sm = false \/ ~In src destroyed_at_move_regs /\ list_disjoint args destroyed_at_move_regs).
    destruct SAFE. auto. right. 
    destruct (list_disjoint_dec mreg_eq (src :: args) destroyed_at_move_regs); try discriminate.
    split. eapply list_disjoint_notin; eauto with coqlib. eapply list_disjoint_cons_left; eauto. 
  left; econstructor; split.
  econstructor.  instantiate (1 := a).  rewrite <- H.
  rewrite (agree_regs _ _ _ args AG). 
  apply eval_addressing_preserved.  exact symbols_preserved.
  tauto.
  rewrite (agree_reg _ _ _ src AG).
  eauto.
  tauto.
  apply match_states_regular with false; auto.
  apply kill_temps_hold; auto.
  eapply agree_undef_temps; eauto.

(* call *)
  simpl in SAFE. assert (sm = false) by intuition congruence. 
  subst sm. rewrite agree_false in AG. subst rs'. 
  left; econstructor; split.
  constructor. eapply find_function_translated; eauto. 
  symmetry; apply sig_preserved.
  constructor. constructor; auto. constructor. 

(* tailcall *)
  simpl in SAFE. assert (sm = false) by intuition congruence. 
  subst sm. rewrite agree_false in AG. subst rs'. 
  left; econstructor; split.
  constructor. eapply find_function_translated; eauto. 
  symmetry; apply sig_preserved. eauto. 
  rewrite (match_parent_locset _ _ STK). constructor; auto.

(* builtin *)
  left; econstructor; split.
  constructor.
  rewrite (agree_regs _ _ _ args AG). 
  eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
  simpl in SAFE. destruct (list_disjoint_dec mreg_eq args destroyed_at_move_regs); simpl in SAFE; intuition congruence.
  apply match_states_regular with false; auto.
  apply kill_loc_hold; apply kill_temps_hold; auto.
  apply agree_set. eapply agree_undef_temps; eauto.

(* annot *)
  simpl in SAFE. assert (sm = false) by intuition congruence. 
  subst sm. rewrite agree_false in AG. subst rs'. 
  left; econstructor; split.
  econstructor. eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
  apply match_states_regular with false; auto.
  rewrite agree_false; auto. 

(* label *)
  left; econstructor; split. constructor.
  apply match_states_regular with false; auto. 
  apply nil_hold.
  simpl in SAFE. destruct SAFE. subst sm. auto. congruence.

(* goto *)
  generalize (transl_find_label lbl (fn_code f) nil).  rewrite H. simpl. intros.
  left; econstructor; split. constructor; eauto.
  apply match_states_regular with false; auto. 
  apply nil_hold.
  simpl in SAFE. destruct SAFE. subst sm. auto. congruence.

(* cond true *)
  generalize (transl_find_label lbl (fn_code f) nil).  rewrite H0. simpl. intros.
  left; econstructor; split.
  apply exec_Lcond_true; auto.
  rewrite (agree_regs _ _ _ args AG). auto.
  simpl in SAFE. destruct (list_disjoint_dec mreg_eq args destroyed_at_move_regs); simpl in SAFE; intuition congruence.
  eauto.
  apply match_states_regular with false; auto.
  apply nil_hold. 
  eapply agree_undef_temps; eauto.

(* cond false *)
  left; econstructor; split. apply exec_Lcond_false; auto.
  rewrite (agree_regs _ _ _ args AG). auto.
  simpl in SAFE. destruct (list_disjoint_dec mreg_eq args destroyed_at_move_regs); simpl in SAFE; intuition congruence.
  apply match_states_regular with false; auto.
  apply kill_temps_hold; auto.
  eapply agree_undef_temps; eauto.

(* jumptable *)
  generalize (transl_find_label lbl (fn_code f) nil).  rewrite H1. simpl. intros.
  left; econstructor; split. econstructor; eauto.
  rewrite (agree_reg _ _ _ arg AG). auto.
  simpl in SAFE. destruct (in_dec mreg_eq arg destroyed_at_move_regs); simpl in SAFE; intuition congruence.
  apply match_states_regular with false; auto.
  apply nil_hold.
  eapply agree_undef_temps; eauto.

(* return *)
  simpl in SAFE. destruct SAFE; try discriminate. subst sm. rewrite agree_false in AG. subst rs'.
  left; econstructor; split.
  constructor. simpl. eauto. 
  rewrite (match_parent_locset _ _ STK). 
  constructor; auto.

(* internal *)
  left; econstructor; split.
  constructor. simpl; eauto.
  simpl. apply match_states_regular with false; auto. apply nil_hold. rewrite agree_false; auto.

(* external *)
  left; econstructor; split.
  econstructor. eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved. 
  auto. eauto. 
  constructor; auto. 

(* return *)
  inv STK. inv H1. left; econstructor; split. constructor.
  apply match_states_regular with false; auto.
  apply nil_hold.
  rewrite agree_false; auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  econstructor; split.
  econstructor.
  apply Genv.init_mem_transf; eauto.
  rewrite symbols_preserved. eauto.
  apply function_ptr_translated; eauto. 
  rewrite sig_preserved. auto.
  econstructor; eauto. constructor.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STK. econstructor. auto.
Qed.

Theorem transf_program_correct:
  forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
Proof.
  eapply forward_simulation_opt.
  eexact symbols_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact transf_step_correct. 
Qed.

End PRESERVATION.

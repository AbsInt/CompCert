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

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Memory.
Require Import Events.
Require Import Op.
Require Import Machregs.
Require Import Locations.
Require Import Conventions.
Require Import LTL.
Require Import Linear.

(** The rules are presented as boolean-valued functions so that we
  get an executable type-checker for free. *)

Section WT_INSTR.

Variable funct: function.

Definition slot_valid (sl: slot) (ofs: Z) (ty: typ): bool :=
  match sl with
  | Local => zle 0 ofs
  | Outgoing => zle 0 ofs
  | Incoming => In_dec Loc.eq (S Incoming ofs ty) (regs_of_rpairs (loc_parameters funct.(fn_sig)))
  end
  && Zdivide_dec (typealign ty) ofs (typealign_pos ty).

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

Fixpoint wt_builtin_res (ty: typ) (res: builtin_res mreg) : bool :=
  match res with
  | BR r => subtype ty (mreg_type r)
  | BR_none => true
  | BR_splitlong hi lo => wt_builtin_res Tint hi && wt_builtin_res Tint lo
  end.

Definition wt_instr (i: instruction) : bool :=
  match i with
  | Lgetstack sl ofs ty r =>
      subtype ty (mreg_type r) && slot_valid sl ofs ty
  | Lsetstack r sl ofs ty =>
      slot_valid sl ofs ty && slot_writable sl
  | Lop op args res =>
      match is_move_operation op args with
      | Some arg =>
          subtype (mreg_type arg) (mreg_type res)
      | None =>
          let (targs, tres) := type_of_operation op in
          subtype tres (mreg_type res)
      end
  | Lload chunk addr args dst =>
      subtype (type_of_chunk chunk) (mreg_type dst)
  | Ltailcall sg ros =>
      zeq (size_arguments sg) 0
  | Lbuiltin ef args res =>
      wt_builtin_res (proj_sig_res (ef_sig ef)) res
      && forallb loc_valid (params_of_builtin_args args)
  | _ =>
      true
  end.

End WT_INSTR.

Definition wt_code (f: function) (c: code) : bool :=
  forallb (wt_instr f) c.

Definition wt_function (f: function) : bool :=
  wt_code f f.(fn_code).

(** Typing the run-time state. *)

Definition wt_locset (ls: locset) : Prop :=
  forall l, Val.has_type (ls l) (Loc.type l).

Lemma wt_setreg:
  forall ls r v,
  Val.has_type v (mreg_type r) -> wt_locset ls -> wt_locset (Locmap.set (R r) v ls).
Proof.
  intros; red; intros.
  unfold Locmap.set.
  destruct (Loc.eq (R r) l).
  subst l; auto.
  destruct (Loc.diff_dec (R r) l). auto. red. auto.
Qed.

Lemma wt_setstack:
  forall ls sl ofs ty v,
  wt_locset ls -> wt_locset (Locmap.set (S sl ofs ty) v ls).
Proof.
  intros; red; intros.
  unfold Locmap.set.
  destruct (Loc.eq (S sl ofs ty) l).
  subst l. simpl.
  generalize (Val.load_result_type (chunk_of_type ty) v).
  replace (type_of_chunk (chunk_of_type ty)) with ty. auto.
  destruct ty; reflexivity.
  destruct (Loc.diff_dec (S sl ofs ty) l). auto. red. auto.
Qed.

Lemma wt_undef_regs:
  forall rs ls, wt_locset ls -> wt_locset (undef_regs rs ls).
Proof.
  induction rs; simpl; intros. auto. apply wt_setreg; auto. red; auto.
Qed.

Lemma wt_call_regs:
  forall ls, wt_locset ls -> wt_locset (call_regs ls).
Proof.
  intros; red; intros. unfold call_regs. destruct l. auto.
  destruct sl.
  red; auto.
  change (Loc.type (S Incoming pos ty)) with (Loc.type (S Outgoing pos ty)). auto.
  red; auto.
Qed.

Lemma wt_return_regs:
  forall caller callee,
  wt_locset caller -> wt_locset callee -> wt_locset (return_regs caller callee).
Proof.
  intros; red; intros.
  unfold return_regs. destruct l.
- destruct (is_callee_save r); auto.
- destruct sl; auto; red; auto.
Qed.

Lemma wt_undef_caller_save_regs:
  forall ls, wt_locset ls -> wt_locset (undef_caller_save_regs ls).
Proof.
  intros; red; intros. unfold undef_caller_save_regs.
  destruct l.
  destruct (is_callee_save r); auto; simpl; auto.
  destruct sl; auto; red; auto. 
Qed.

Lemma wt_init:
  wt_locset (Locmap.init Vundef).
Proof.
  red; intros. unfold Locmap.init. red; auto.
Qed.

Lemma wt_setpair:
  forall sg v rs,
  Val.has_type v (proj_sig_res sg) ->
  wt_locset rs ->
  wt_locset (Locmap.setpair (loc_result sg) v rs).
Proof.
  intros. generalize (loc_result_pair sg) (loc_result_type sg).
  destruct (loc_result sg); simpl Locmap.setpair.
- intros. apply wt_setreg; auto. eapply Val.has_subtype; eauto.
- intros A B. decompose [and] A.
  apply wt_setreg. eapply Val.has_subtype; eauto. destruct v; exact I.
  apply wt_setreg. eapply Val.has_subtype; eauto. destruct v; exact I.
  auto.
Qed.

Lemma wt_setres:
  forall res ty v rs,
  wt_builtin_res ty res = true ->
  Val.has_type v ty ->
  wt_locset rs ->
  wt_locset (Locmap.setres res v rs).
Proof.
  induction res; simpl; intros.
- apply wt_setreg; auto. eapply Val.has_subtype; eauto.
- auto.
- InvBooleans. eapply IHres2; eauto. destruct v; exact I.
  eapply IHres1; eauto. destruct v; exact I.
Qed.

Lemma wt_find_label:
  forall f lbl c,
  wt_function f = true ->
  find_label lbl f.(fn_code) = Some c ->
  wt_code f c = true.
Proof.
  unfold wt_function; intros until c. generalize (fn_code f). induction c0; simpl; intros.
  discriminate.
  InvBooleans. destruct (is_label lbl a).
  congruence.
  auto.
Qed.

(** In addition to type preservation during evaluation, we also show
  properties of the environment [ls] at call points and at return points.
  These properties are used in the proof of the [Stacking] pass.
  For call points, we have that the current environment [ls] and the
  one from the top call stack agree on the [Outgoing] locations
  used for parameter passing. *)

Definition agree_outgoing_arguments (sg: signature) (ls pls: locset) : Prop :=
  forall ty ofs,
  In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) ->
  ls (S Outgoing ofs ty) = pls (S Outgoing ofs ty).

(** For return points, we have that all [Outgoing] stack locations have
  been set to [Vundef]. *)

Definition outgoing_undef (ls: locset) : Prop :=
  forall ty ofs, ls (S Outgoing ofs ty) = Vundef.

(** Soundness of the type system *)

Definition wt_fundef (fd: fundef) :=
  match fd with
  | Internal f => wt_function f = true
  | External ef => True
  end.

Inductive wt_callstack: list stackframe -> Prop :=
  | wt_callstack_nil:
      wt_callstack nil
  | wt_callstack_cons: forall f sp rs c s
        (WTSTK: wt_callstack s)
        (WTF: wt_function f = true)
        (WTC: wt_code f c = true)
        (WTRS: wt_locset rs),
      wt_callstack (Stackframe f sp rs c :: s).

Lemma wt_parent_locset:
  forall s, wt_callstack s -> wt_locset (parent_locset s).
Proof.
  induction 1; simpl.
- apply wt_init.
- auto.
Qed.

Inductive wt_state: state -> Prop :=
  | wt_regular_state: forall s f sp c rs m
        (WTSTK: wt_callstack s )
        (WTF: wt_function f = true)
        (WTC: wt_code f c = true)
        (WTRS: wt_locset rs),
      wt_state (State s f sp c rs m)
  | wt_call_state: forall s fd rs m
        (WTSTK: wt_callstack s)
        (WTFD: wt_fundef fd)
        (WTRS: wt_locset rs)
        (AGCS: agree_callee_save rs (parent_locset s))
        (AGARGS: agree_outgoing_arguments (funsig fd) rs (parent_locset s)),
      wt_state (Callstate s fd rs m)
  | wt_return_state: forall s rs m
        (WTSTK: wt_callstack s)
        (WTRS: wt_locset rs)
        (AGCS: agree_callee_save rs (parent_locset s))
        (UOUT: outgoing_undef rs),
      wt_state (Returnstate s rs m).

(** Preservation of state typing by transitions *)

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
Local Opaque mreg_type.
  induction 1; intros WTS; inv WTS.
- (* getstack *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  eapply wt_setreg; eauto. eapply Val.has_subtype; eauto. apply WTRS.
  apply wt_undef_regs; auto.
- (* setstack *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  apply wt_setstack. apply wt_undef_regs; auto.
- (* op *)
  simpl in *. destruct (is_move_operation op args) as [src | ] eqn:ISMOVE.
  + (* move *)
    InvBooleans. exploit is_move_operation_correct; eauto. intros [EQ1 EQ2]; subst.
    simpl in H. inv H.
    econstructor; eauto. apply wt_setreg. eapply Val.has_subtype; eauto. apply WTRS.
    apply wt_undef_regs; auto.
  + (* other ops *)
    destruct (type_of_operation op) as [ty_args ty_res] eqn:TYOP. InvBooleans.
    econstructor; eauto.
    apply wt_setreg; auto. eapply Val.has_subtype; eauto.
    change ty_res with (snd (ty_args, ty_res)). rewrite <- TYOP. eapply type_of_operation_sound; eauto.
    red; intros; subst op. simpl in ISMOVE.
    destruct args; try discriminate. destruct args; discriminate.
    apply wt_undef_regs; auto.
- (* load *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  apply wt_setreg. eapply Val.has_subtype; eauto.
  destruct a; simpl in H0; try discriminate. eapply Mem.load_type; eauto.
  apply wt_undef_regs; auto.
- (* store *)
  simpl in *; InvBooleans.
  econstructor. eauto. eauto. eauto.
  apply wt_undef_regs; auto.
- (* call *)
  simpl in *; InvBooleans.
  econstructor; eauto. econstructor; eauto.
  eapply wt_find_function; eauto.
  red; simpl; auto.
  red; simpl; auto.
- (* tailcall *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  eapply wt_find_function; eauto.
  apply wt_return_regs; auto. apply wt_parent_locset; auto.
  red; simpl; intros. destruct l; simpl in *. rewrite H3; auto. destruct sl; auto; congruence.
  red; simpl; intros. apply zero_size_arguments_tailcall_possible in H. apply H in H3. contradiction.
- (* builtin *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  eapply wt_setres; eauto. eapply external_call_well_typed; eauto.
  apply wt_undef_regs; auto.
- (* label *)
  simpl in *. econstructor; eauto.
- (* goto *)
  simpl in *. econstructor; eauto. eapply wt_find_label; eauto.
- (* cond branch, taken *)
  simpl in *. econstructor. auto. auto. eapply wt_find_label; eauto.
  apply wt_undef_regs; auto.
- (* cond branch, not taken *)
  simpl in *. econstructor. auto. auto. auto.
  apply wt_undef_regs; auto.
- (* jumptable *)
  simpl in *. econstructor. auto. auto. eapply wt_find_label; eauto.
  apply wt_undef_regs; auto.
- (* return *)
  simpl in *. InvBooleans.
  econstructor; eauto.
  apply wt_return_regs; auto. apply wt_parent_locset; auto.
  red; simpl; intros. destruct l; simpl in *. rewrite H0; auto. destruct sl; auto; congruence.
  red; simpl; intros. auto.
- (* internal function *)
  simpl in WTFD.
  econstructor. eauto. eauto. eauto.
  apply wt_undef_regs. apply wt_call_regs. auto.
- (* external function *)
  econstructor. auto. apply wt_setpair. 
  eapply external_call_well_typed; eauto.
  apply wt_undef_caller_save_regs; auto.
  red; simpl; intros. destruct l; simpl in *.
  rewrite locmap_get_set_loc_result by auto. simpl. rewrite H; auto. 
  rewrite locmap_get_set_loc_result by auto. simpl. destruct sl; auto; congruence.
  red; simpl; intros. rewrite locmap_get_set_loc_result by auto. auto.
- (* return *)
  inv WTSTK. econstructor; eauto.
Qed.

Theorem wt_initial_state:
  forall S, initial_state prog S -> wt_state S.
Proof.
  induction 1. econstructor. constructor.
  unfold ge0 in H1. exploit Genv.find_funct_ptr_inversion; eauto.
  intros [id IN]. eapply wt_prog; eauto.
  apply wt_init.
  red; auto.
  red; auto.
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
  slot_valid f sl ofs ty = true /\ slot_writable sl = true.
Proof.
  intros. inv H. simpl in WTC; InvBooleans. intuition.
Qed.

Lemma wt_state_tailcall:
  forall s f sp sg ros c rs m,
  wt_state (State s f sp (Ltailcall sg ros :: c) rs m) ->
  size_arguments sg = 0.
Proof.
  intros. inv H. simpl in WTC; InvBooleans. auto.
Qed.

Lemma wt_state_builtin:
  forall s f sp ef args res c rs m,
  wt_state (State s f sp (Lbuiltin ef args res :: c) rs m) ->
  forallb (loc_valid f) (params_of_builtin_args args) = true.
Proof.
  intros. inv H. simpl in WTC; InvBooleans. auto.
Qed.

Lemma wt_callstate_wt_regs:
  forall s f rs m,
  wt_state (Callstate s f rs m) ->
  forall r, Val.has_type (rs (R r)) (mreg_type r).
Proof.
  intros. inv H. apply WTRS.
Qed.

Lemma wt_callstate_agree:
  forall s f rs m,
  wt_state (Callstate s f rs m) ->
  agree_callee_save rs (parent_locset s) /\ agree_outgoing_arguments (funsig f) rs (parent_locset s).
Proof.
  intros. inv H; auto.
Qed.

Lemma wt_returnstate_agree:
  forall s rs m,
  wt_state (Returnstate s rs m) ->
  agree_callee_save rs (parent_locset s) /\ outgoing_undef rs.
Proof.
  intros. inv H; auto.
Qed.

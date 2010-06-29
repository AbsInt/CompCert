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

(** Correctness of instruction selection *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.
Require Import Selection.
Require Import SelectOpproof.

Open Local Scope cminorsel_scope.

(** * Correctness of the instruction selection functions for expressions *)

Section CMCONSTR.

Variable ge: genv.
Variable sp: val.
Variable e: env.
Variable m: mem.

(** Conversion of condition expressions. *)

Lemma negate_condexpr_correct:
  forall le a b,
  eval_condexpr ge sp e m le a b ->
  eval_condexpr ge sp e m le (negate_condexpr a) (negb b).
Proof.
  induction 1; simpl.
  constructor.
  constructor.
  econstructor. eauto. apply eval_negate_condition. auto.
  econstructor. eauto. destruct vb1; auto.
Qed. 

Scheme expr_ind2 := Induction for expr Sort Prop
  with exprlist_ind2 := Induction for exprlist Sort Prop.

Fixpoint forall_exprlist (P: expr -> Prop) (el: exprlist) {struct el}: Prop :=
  match el with
  | Enil => True
  | Econs e el' => P e /\ forall_exprlist P el'
  end.

Lemma expr_induction_principle:
  forall (P: expr -> Prop),
  (forall i : ident, P (Evar i)) ->
  (forall (o : operation) (e : exprlist),
     forall_exprlist P e -> P (Eop o e)) ->
  (forall (m : memory_chunk) (a : Op.addressing) (e : exprlist),
     forall_exprlist P e -> P (Eload m a e)) ->
  (forall (c : condexpr) (e : expr),
     P e -> forall e0 : expr, P e0 -> P (Econdition c e e0)) ->
  (forall e : expr, P e -> forall e0 : expr, P e0 -> P (Elet e e0)) ->
  (forall n : nat, P (Eletvar n)) ->
  forall e : expr, P e.
Proof.
  intros. apply expr_ind2 with (P := P) (P0 := forall_exprlist P); auto.
  simpl. auto.
  intros. simpl. auto.
Qed.

Lemma eval_base_condition_of_expr:
  forall le a v b,
  eval_expr ge sp e m le a v ->
  Val.bool_of_val v b ->
  eval_condexpr ge sp e m le 
                (CEcond (Ccompimm Cne Int.zero) (a ::: Enil))
                b.
Proof.
  intros. 
  eapply eval_CEcond. eauto with evalexpr. 
  inversion H0; simpl. rewrite Int.eq_false; auto. auto. auto.
Qed.

Lemma is_compare_neq_zero_correct:
  forall c v b,
  is_compare_neq_zero c = true ->
  eval_condition c (v :: nil) = Some b ->
  Val.bool_of_val v b.
Proof.
  intros.
  destruct c; simpl in H; try discriminate;
  destruct c; simpl in H; try discriminate;
  generalize (Int.eq_spec i Int.zero); rewrite H; intro; subst i.

  simpl in H0. destruct v; inv H0. 
  generalize (Int.eq_spec i Int.zero). destruct (Int.eq i Int.zero); intros; simpl.
  subst i; constructor. constructor; auto. constructor.

  simpl in H0. destruct v; inv H0. 
  generalize (Int.eq_spec i Int.zero). destruct (Int.eq i Int.zero); intros; simpl.
  subst i; constructor. constructor; auto.
Qed.

Lemma is_compare_eq_zero_correct:
  forall c v b,
  is_compare_eq_zero c = true ->
  eval_condition c (v :: nil) = Some b ->
  Val.bool_of_val v (negb b).
Proof.
  intros. apply is_compare_neq_zero_correct with (negate_condition c).
  destruct c; simpl in H; simpl; try discriminate;
  destruct c; simpl; try discriminate; auto.
  apply eval_negate_condition; auto.
Qed.

Lemma eval_condition_of_expr:
  forall a le v b,
  eval_expr ge sp e m le a v ->
  Val.bool_of_val v b ->
  eval_condexpr ge sp e m le (condexpr_of_expr a) b.
Proof.
  intro a0; pattern a0.
  apply expr_induction_principle; simpl; intros;
    try (eapply eval_base_condition_of_expr; eauto; fail).
  
  destruct o; try (eapply eval_base_condition_of_expr; eauto; fail).

  destruct e0. inv H0. inv H5. simpl in H7. inv H7.  
  inversion H1. 
  rewrite Int.eq_false; auto. constructor.
  subst i; rewrite Int.eq_true. constructor.
  eapply eval_base_condition_of_expr; eauto.

  inv H0. simpl in H7.
  assert (eval_condition c vl = Some b).
    destruct (eval_condition c vl); try discriminate.
    destruct b0; inv H7; inversion H1; congruence.
  assert (eval_condexpr ge sp e m le (CEcond c e0) b).
    eapply eval_CEcond; eauto.
  destruct e0; auto. destruct e1; auto.
  simpl in H. destruct H.
  inv H5. inv H11.

  case_eq (is_compare_neq_zero c); intros.
  eapply H; eauto.
  apply is_compare_neq_zero_correct with c; auto.

  case_eq (is_compare_eq_zero c); intros.
  replace b with (negb (negb b)). apply negate_condexpr_correct.
  eapply H; eauto.
  apply is_compare_eq_zero_correct with c; auto.
  apply negb_involutive.

  auto.

  inv H1. destruct v1; eauto with evalexpr.
Qed.

Lemma eval_load:
  forall le a v chunk v',
  eval_expr ge sp e m le a v ->
  Mem.loadv chunk m v = Some v' ->
  eval_expr ge sp e m le (load chunk a) v'.
Proof.
  intros. generalize H0; destruct v; simpl; intro; try discriminate.
  unfold load. 
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (refl_equal _)).
  destruct (addressing chunk a). intros [vl [EV EQ]]. 
  eapply eval_Eload; eauto. 
Qed.

Lemma eval_store:
  forall chunk a1 a2 v1 v2 f k m',
  eval_expr ge sp e m nil a1 v1 ->
  eval_expr ge sp e m nil a2 v2 ->
  Mem.storev chunk m v1 v2 = Some m' ->
  step ge (State f (store chunk a1 a2) k sp e m)
       E0 (State f Sskip k sp e m').
Proof.
  intros. generalize H1; destruct v1; simpl; intro; try discriminate.
  unfold store.
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (refl_equal _)).
  destruct (addressing chunk a1). intros [vl [EV EQ]]. 
  eapply step_store; eauto. 
Qed.

(** Correctness of instruction selection for operators *)

Lemma eval_sel_unop:
  forall le op a1 v1 v,
  eval_expr ge sp e m le a1 v1 ->
  eval_unop op v1 = Some v ->
  eval_expr ge sp e m le (sel_unop op a1) v.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_cast8unsigned; auto.
  apply eval_cast8signed; auto.
  apply eval_cast16unsigned; auto.
  apply eval_cast16signed; auto.
  apply eval_negint; auto.
  generalize (Int.eq_spec i Int.zero). destruct (Int.eq i Int.zero); intro.
  change true with (negb false). eapply eval_notbool; eauto. subst i; constructor.
  change false with (negb true). eapply eval_notbool; eauto. constructor; auto.
  change Vfalse with (Val.of_bool (negb true)).
  eapply eval_notbool; eauto. constructor.
  apply eval_notint; auto.
  apply eval_negf; auto.
  apply eval_absf; auto.
  apply eval_singleoffloat; auto.
  apply eval_intoffloat; auto.
  apply eval_intuoffloat; auto.
  apply eval_floatofint; auto.
  apply eval_floatofintu; auto.
Qed.

Lemma eval_sel_binop:
  forall le op a1 a2 v1 v2 v,
  eval_expr ge sp e m le a1 v1 ->
  eval_expr ge sp e m le a2 v2 ->
  eval_binop op v1 v2 = Some v ->
  eval_expr ge sp e m le (sel_binop op a1 a2) v.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_add; auto.
  apply eval_add_ptr_2; auto.
  apply eval_add_ptr; auto.
  apply eval_sub; auto.
  apply eval_sub_ptr_int; auto.
  destruct (eq_block b b0); inv H1. 
  eapply eval_sub_ptr_ptr; eauto.
  apply eval_mul; eauto.
  generalize (Int.eq_spec i0 Int.zero). destruct (Int.eq i0 Int.zero); inv H1.
  apply eval_divs; eauto.
  generalize (Int.eq_spec i0 Int.zero). destruct (Int.eq i0 Int.zero); inv H1.
  apply eval_divu; eauto.
  generalize (Int.eq_spec i0 Int.zero). destruct (Int.eq i0 Int.zero); inv H1.
  apply eval_mods; eauto.
  generalize (Int.eq_spec i0 Int.zero). destruct (Int.eq i0 Int.zero); inv H1.
  apply eval_modu; eauto.
  apply eval_and; auto.
  apply eval_or; auto.
  apply eval_xor; auto.
  caseEq (Int.ltu i0 Int.iwordsize); intro; rewrite H2 in H1; inv H1.
  apply eval_shl; auto.
  caseEq (Int.ltu i0 Int.iwordsize); intro; rewrite H2 in H1; inv H1.
  apply eval_shr; auto.
  caseEq (Int.ltu i0 Int.iwordsize); intro; rewrite H2 in H1; inv H1.
  apply eval_shru; auto.
  apply eval_addf; auto.
  apply eval_subf; auto.
  apply eval_mulf; auto.
  apply eval_divf; auto.
  apply eval_comp_int; auto.
  eapply eval_comp_int_ptr; eauto.
  eapply eval_comp_ptr_int; eauto.
  destruct (eq_block b b0); inv H1.
  eapply eval_comp_ptr_ptr; eauto.
  eapply eval_comp_ptr_ptr_2; eauto.
  eapply eval_compu; eauto.
  eapply eval_compf; eauto.
Qed.

End CMCONSTR.

(** Recognition of calls to built-in functions *)

Lemma expr_is_addrof_ident_correct:
  forall e id,
  expr_is_addrof_ident e = Some id ->
  e = Cminor.Econst (Cminor.Oaddrsymbol id Int.zero).
Proof.
  intros e id. unfold expr_is_addrof_ident. 
  destruct e; try congruence.
  destruct c; try congruence.
  predSpec Int.eq Int.eq_spec i0 Int.zero; congruence.
Qed.

Lemma expr_is_addrof_builtin_correct:
  forall ge sp e m a v ef fd,
  expr_is_addrof_builtin ge a = Some ef ->
  Cminor.eval_expr ge sp e m a v ->
  Genv.find_funct ge v = Some fd ->
  fd = External ef.
Proof.
  intros until fd; unfold expr_is_addrof_builtin.
  case_eq (expr_is_addrof_ident a); intros; try congruence.
  exploit expr_is_addrof_ident_correct; eauto. intro EQ; subst a.
  inv H1. inv H4. 
  destruct (Genv.find_symbol ge i); try congruence.
  inv H3. rewrite Genv.find_funct_find_funct_ptr in H2. rewrite H2 in H0. 
  destruct fd; try congruence. 
  destruct (ef_inline e0); congruence.
Qed.

(** * Semantic preservation for instruction selection. *)

Section PRESERVATION.

Variable prog: Cminor.program.
Let tprog := sel_program prog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

(** Relationship between the global environments for the original
  CminorSel program and the generated RTL program. *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros; unfold ge, tge, tprog, sel_program. 
  apply Genv.find_symbol_transf.
Qed.

Lemma functions_translated:
  forall (v: val) (f: Cminor.fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (sel_fundef ge f).
Proof.  
  intros.
  exact (Genv.find_funct_transf (sel_fundef ge) _ _ H).
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: Cminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (sel_fundef ge f).
Proof.  
  intros. 
  exact (Genv.find_funct_ptr_transf (sel_fundef ge) _ _ H).
Qed.

Lemma sig_function_translated:
  forall f,
  funsig (sel_fundef ge f) = Cminor.funsig f.
Proof.
  intros. destruct f; reflexivity.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros; unfold ge, tge, tprog, sel_program. 
  apply Genv.find_var_info_transf.
Qed.

(** Semantic preservation for expressions. *)

Lemma sel_expr_correct:
  forall sp e m a v,
  Cminor.eval_expr ge sp e m a v ->
  forall le,
  eval_expr tge sp e m le (sel_expr a) v.
Proof.
  induction 1; intros; simpl.
  (* Evar *)
  constructor; auto.
  (* Econst *)
  destruct cst; simpl; simpl in H; (econstructor; [constructor|simpl;auto]).
  rewrite symbols_preserved. auto.
  (* Eunop *)
  eapply eval_sel_unop; eauto.
  (* Ebinop *)
  eapply eval_sel_binop; eauto.
  (* Eload *)
  eapply eval_load; eauto.
  (* Econdition *)
  econstructor; eauto. eapply eval_condition_of_expr; eauto. 
  destruct b1; auto.
Qed.

Hint Resolve sel_expr_correct: evalexpr.

Lemma sel_exprlist_correct:
  forall sp e m a v,
  Cminor.eval_exprlist ge sp e m a v ->
  forall le,
  eval_exprlist tge sp e m le (sel_exprlist a) v.
Proof.
  induction 1; intros; simpl; constructor; auto with evalexpr.
Qed.

Hint Resolve sel_exprlist_correct: evalexpr.

(** Semantic preservation for terminating function calls and statements. *)

Fixpoint sel_cont (k: Cminor.cont) : CminorSel.cont :=
  match k with
  | Cminor.Kstop => Kstop
  | Cminor.Kseq s1 k1 => Kseq (sel_stmt ge s1) (sel_cont k1)
  | Cminor.Kblock k1 => Kblock (sel_cont k1)
  | Cminor.Kcall id f sp e k1 =>
      Kcall id (sel_function ge f) sp e (sel_cont k1)
  end.

Inductive match_states: Cminor.state -> CminorSel.state -> Prop :=
  | match_state: forall f s k s' k' sp e m,
      s' = sel_stmt ge s ->
      k' = sel_cont k ->
      match_states
        (Cminor.State f s k sp e m)
        (State (sel_function ge f) s' k' sp e m)
  | match_callstate: forall f args k k' m,
      k' = sel_cont k ->
      match_states
        (Cminor.Callstate f args k m)
        (Callstate (sel_fundef ge f) args k' m)
  | match_returnstate: forall v k k' m,
      k' = sel_cont k ->
      match_states
        (Cminor.Returnstate v k m)
        (Returnstate v k' m)
  | match_builtin_1: forall ef args optid f sp e k m al k',
      k' = sel_cont k ->
      eval_exprlist tge sp e m nil al args ->
      match_states
        (Cminor.Callstate (External ef) args (Cminor.Kcall optid f sp e k) m)
        (State (sel_function ge f) (Sbuiltin optid ef al) k' sp e m)
  | match_builtin_2: forall v optid f sp e k m k',
      k' = sel_cont k ->
      match_states
        (Cminor.Returnstate v (Cminor.Kcall optid f sp e k) m)
        (State (sel_function ge f) Sskip k' sp (set_optvar optid v e) m).

Remark call_cont_commut:
  forall k, call_cont (sel_cont k) = sel_cont (Cminor.call_cont k).
Proof.
  induction k; simpl; auto.
Qed.

Remark find_label_commut:
  forall lbl s k,
  find_label lbl (sel_stmt ge s) (sel_cont k) =
  option_map (fun sk => (sel_stmt ge (fst sk), sel_cont (snd sk)))
             (Cminor.find_label lbl s k).
Proof.
  induction s; intros; simpl; auto.
  unfold store. destruct (addressing m (sel_expr e)); auto.
  destruct (expr_is_addrof_builtin ge e); auto.
  change (Kseq (sel_stmt ge s2) (sel_cont k))
    with (sel_cont (Cminor.Kseq s2 k)).
  rewrite IHs1. rewrite IHs2. 
  destruct (Cminor.find_label lbl s1 (Cminor.Kseq s2 k)); auto.
  rewrite IHs1. rewrite IHs2. 
  destruct (Cminor.find_label lbl s1 k); auto.
  change (Kseq (Sloop (sel_stmt ge s)) (sel_cont k))
    with (sel_cont (Cminor.Kseq (Cminor.Sloop s) k)).
  auto.
  change (Kblock (sel_cont k))
    with (sel_cont (Cminor.Kblock k)).
  auto.
  destruct o; auto.
  destruct (ident_eq lbl l); auto.
Qed.

Definition measure (s: Cminor.state) : nat :=
  match s with
  | Cminor.Callstate _ _ _ _ => 0%nat
  | Cminor.State _ _ _ _ _ _ => 1%nat
  | Cminor.Returnstate _ _ _ => 2%nat
  end.

Lemma sel_step_correct:
  forall S1 t S2, Cminor.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
  (exists T2, step tge T1 t T2 /\ match_states S2 T2)
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 T1)%nat.
Proof.
  induction 1; intros T1 ME; inv ME; simpl;
  try (left; econstructor; split; [econstructor; eauto with evalexpr | econstructor; eauto]; fail).

  (* skip call *)
  left; econstructor; split. 
  econstructor. destruct k; simpl in H; simpl; auto. 
  rewrite <- H0; reflexivity.
  simpl. eauto. 
  constructor; auto.
  (* store *)
  left; econstructor; split.
  eapply eval_store; eauto with evalexpr.
  constructor; auto.
  (* Scall *)
  case_eq (expr_is_addrof_builtin ge a).
  (* Scall turned into Sbuiltin *)
  intros ef EQ. exploit expr_is_addrof_builtin_correct; eauto. intro EQ1. subst fd.
  right; split. omega. split. auto. 
  econstructor; eauto with evalexpr.
  (* Scall preserved *)
  intro EQ. left; econstructor; split.
  econstructor; eauto with evalexpr.
  apply functions_translated; eauto. 
  apply sig_function_translated.
  constructor; auto.
  (* Stailcall *)
  left; econstructor; split.
  econstructor; eauto with evalexpr.
  apply functions_translated; eauto. 
  apply sig_function_translated.
  constructor; auto. apply call_cont_commut.
  (* Sifthenelse *)
  left; exists (State (sel_function ge f) (if b then sel_stmt ge s1 else sel_stmt ge s2) (sel_cont k) sp e m); split.
  constructor. eapply eval_condition_of_expr; eauto with evalexpr.
  constructor; auto. destruct b; auto.
  (* Sreturn None *)
  left; econstructor; split. 
  econstructor. simpl; eauto. 
  constructor; auto. apply call_cont_commut.
  (* Sreturn Some *)
  left; econstructor; split. 
  econstructor. simpl. eauto with evalexpr. simpl; eauto.
  constructor; auto. apply call_cont_commut.
  (* Sgoto *)
  left; econstructor; split.
  econstructor. simpl. rewrite call_cont_commut. rewrite find_label_commut.
  rewrite H. simpl. reflexivity. 
  constructor; auto.
  (* external call *)
  left; econstructor; split.
  econstructor. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.
  (* external call turned into a Sbuiltin *)
  left; econstructor; split.
  econstructor. eauto. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.
  (* return of an external call turned into a Sbuiltin *)
  right; split. omega. split. auto. constructor; auto.
Qed.

Lemma sel_initial_states:
  forall S, Cminor.initial_state prog S ->
  exists R, initial_state tprog R /\ match_states S R.
Proof.
  induction 1.
  econstructor; split.
  econstructor.
  apply Genv.init_mem_transf; eauto.
  simpl. fold tge. rewrite symbols_preserved. eexact H0.
  apply function_ptr_translated. eauto. 
  rewrite <- H2. apply sig_function_translated; auto.
  constructor; auto.
Qed.

Lemma sel_final_states:
  forall S R r,
  match_states S R -> Cminor.final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H. simpl. constructor.
Qed.

Theorem transf_program_correct:
  forall (beh: program_behavior), not_wrong beh ->
  Cminor.exec_program prog beh -> CminorSel.exec_program tprog beh.
Proof.
  unfold CminorSel.exec_program, Cminor.exec_program; intros.
  eapply simulation_opt_preservation; eauto.
  eexact sel_initial_states.
  eexact sel_final_states.
  eexact sel_step_correct. 
Qed.

End PRESERVATION.

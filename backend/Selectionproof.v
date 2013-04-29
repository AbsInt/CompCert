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
Require Import Errors.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.
Require Import SelectLong.
Require Import Selection.
Require Import SelectOpproof.
Require Import SelectLongproof.

Open Local Scope cminorsel_scope.


(** * Correctness of the instruction selection functions for expressions *)

Section PRESERVATION.

Variable prog: Cminor.program.
Let ge := Genv.globalenv prog.
Variable hf: helper_functions.
Let tprog := transform_program (sel_fundef hf ge) prog.
Let tge := Genv.globalenv tprog.
Hypothesis HELPERS: i64_helpers_correct tge hf.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros; unfold ge, tge, tprog. apply Genv.find_symbol_transf.
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: Cminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (sel_fundef hf ge f).
Proof.  
  intros. 
  exact (Genv.find_funct_ptr_transf (sel_fundef hf ge) _ _ H).
Qed.

Lemma functions_translated:
  forall (v v': val) (f: Cminor.fundef),
  Genv.find_funct ge v = Some f ->
  Val.lessdef v v' ->
  Genv.find_funct tge v' = Some (sel_fundef hf ge f).
Proof.  
  intros. inv H0.
  exact (Genv.find_funct_transf (sel_fundef hf ge) _ _ H).
  simpl in H. discriminate.
Qed.

Lemma sig_function_translated:
  forall f,
  funsig (sel_fundef hf ge f) = Cminor.funsig f.
Proof.
  intros. destruct f; reflexivity.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros; unfold ge, tge, tprog, sel_program. 
  apply Genv.find_var_info_transf.
Qed.

Lemma helper_implements_preserved:
  forall id sg vargs vres,
  helper_implements ge id sg vargs vres ->
  helper_implements tge id sg vargs vres.
Proof.
  intros. destruct H as (b & ef & A & B & C & D).
  exploit function_ptr_translated; eauto. simpl. intros. 
  exists b; exists ef. 
  split. rewrite symbols_preserved. auto.
  split. auto.
  split. auto.
  intros. eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
Qed.

Lemma builtin_implements_preserved:
  forall id sg vargs vres,
  builtin_implements ge id sg vargs vres ->
  builtin_implements tge id sg vargs vres.
Proof.
  unfold builtin_implements; intros.
  eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
Qed.

Lemma helpers_correct_preserved:
  forall h, i64_helpers_correct ge h -> i64_helpers_correct tge h.
Proof.
  unfold i64_helpers_correct; intros.
  repeat (match goal with [ H: _ /\ _ |- _ /\ _ ] => destruct H; split end);
  intros; try (eapply helper_implements_preserved; eauto);
  try (eapply builtin_implements_preserved; eauto).
Qed.

Section CMCONSTR.

Variable sp: val.
Variable e: env.
Variable m: mem.

Lemma eval_condexpr_of_expr:
  forall a le v b,
  eval_expr tge sp e m le a v ->
  Val.bool_of_val v b ->
  eval_condexpr tge sp e m le (condexpr_of_expr a) b.
Proof.
  intros until a. functional induction (condexpr_of_expr a); intros.
(* compare *)
  inv H. econstructor; eauto. 
  simpl in H6. inv H6. apply Val.bool_of_val_of_optbool. auto.
(* condition *)
  inv H. econstructor; eauto. destruct va; eauto.
(* let *)
  inv H. econstructor; eauto.
(* default *)
  econstructor. constructor. eauto. constructor. 
  simpl. inv H0. auto. auto. 
Qed.

Lemma eval_load:
  forall le a v chunk v',
  eval_expr tge sp e m le a v ->
  Mem.loadv chunk m v = Some v' ->
  eval_expr tge sp e m le (load chunk a) v'.
Proof.
  intros. generalize H0; destruct v; simpl; intro; try discriminate.
  unfold load. 
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (refl_equal _)).
  destruct (addressing chunk a). intros [vl [EV EQ]]. 
  eapply eval_Eload; eauto. 
Qed.

Lemma eval_store:
  forall chunk a1 a2 v1 v2 f k m',
  eval_expr tge sp e m nil a1 v1 ->
  eval_expr tge sp e m nil a2 v2 ->
  Mem.storev chunk m v1 v2 = Some m' ->
  step tge (State f (store chunk a1 a2) k sp e m)
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
  eval_expr tge sp e m le a1 v1 ->
  eval_unop op v1 = Some v ->
  exists v', eval_expr tge sp e m le (sel_unop hf op a1) v' /\ Val.lessdef v v'.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_cast8unsigned; auto.
  apply eval_cast8signed; auto.
  apply eval_cast16unsigned; auto.
  apply eval_cast16signed; auto.
  apply eval_negint; auto.
  apply eval_notint; auto.
  apply eval_negf; auto.
  apply eval_absf; auto.
  apply eval_singleoffloat; auto.
  eapply eval_intoffloat; eauto.
  eapply eval_intuoffloat; eauto.
  eapply eval_floatofint; eauto.
  eapply eval_floatofintu; eauto.
  eapply eval_negl; eauto.
  eapply eval_notl; eauto.
  eapply eval_intoflong; eauto.
  eapply eval_longofint; eauto.
  eapply eval_longofintu; eauto.
  eapply eval_longoffloat; eauto.
  eapply eval_longuoffloat; eauto.
  eapply eval_floatoflong; eauto.
  eapply eval_floatoflongu; eauto.
Qed.

Lemma eval_sel_binop:
  forall le op a1 a2 v1 v2 v,
  eval_expr tge sp e m le a1 v1 ->
  eval_expr tge sp e m le a2 v2 ->
  eval_binop op v1 v2 m = Some v ->
  exists v', eval_expr tge sp e m le (sel_binop hf op a1 a2) v' /\ Val.lessdef v v'.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_add; auto.
  apply eval_sub; auto.
  apply eval_mul; auto.
  eapply eval_divs; eauto.
  eapply eval_divu; eauto.
  eapply eval_mods; eauto.
  eapply eval_modu; eauto.
  apply eval_and; auto.
  apply eval_or; auto.
  apply eval_xor; auto.
  apply eval_shl; auto.
  apply eval_shr; auto.
  apply eval_shru; auto.
  apply eval_addf; auto.
  apply eval_subf; auto.
  apply eval_mulf; auto.
  apply eval_divf; auto.
  eapply eval_addl; eauto.
  eapply eval_subl; eauto.
  eapply eval_mull; eauto.
  eapply eval_divl; eauto.
  eapply eval_divlu; eauto.
  eapply eval_modl; eauto.
  eapply eval_modlu; eauto.
  eapply eval_andl; eauto.
  eapply eval_orl; eauto.
  eapply eval_xorl; eauto.
  eapply eval_shll; eauto.
  eapply eval_shrl; eauto.
  eapply eval_shrlu; eauto.
  apply eval_comp; auto.
  apply eval_compu; auto.
  apply eval_compf; auto.
  exists v; split; auto. eapply eval_cmpl; eauto.
  exists v; split; auto. eapply eval_cmplu; eauto.
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

Lemma classify_call_correct:
  forall sp e m a v fd,
  Cminor.eval_expr ge sp e m a v ->
  Genv.find_funct ge v = Some fd ->
  match classify_call ge a with
  | Call_default => True
  | Call_imm id => exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b Int.zero
  | Call_builtin ef => fd = External ef
  end.
Proof.
  unfold classify_call; intros. 
  destruct (expr_is_addrof_ident a) as [id|] eqn:?. 
  exploit expr_is_addrof_ident_correct; eauto. intros EQ; subst a.
  inv H. inv H2. 
  destruct (Genv.find_symbol ge id) as [b|] eqn:?. 
  rewrite Genv.find_funct_find_funct_ptr in H0. 
  rewrite H0. 
  destruct fd. exists b; auto. 
  destruct (ef_inline e0). auto. exists b; auto.
  simpl in H0. discriminate.
  auto.
Qed.

(** Compatibility of evaluation functions with the "less defined than" relation. *)

Ltac TrivialExists :=
  match goal with
  | [ |- exists v, Some ?x = Some v /\ _ ] => exists x; split; auto
  | _ => idtac
  end.

Lemma eval_unop_lessdef:
  forall op v1 v1' v,
  eval_unop op v1 = Some v -> Val.lessdef v1 v1' ->
  exists v', eval_unop op v1' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until v; intros EV LD. inv LD. 
  exists v; auto.
  destruct op; simpl in *; inv EV; TrivialExists.
Qed.

Lemma eval_binop_lessdef:
  forall op v1 v1' v2 v2' v m m',
  eval_binop op v1 v2 m = Some v -> 
  Val.lessdef v1 v1' -> Val.lessdef v2 v2' -> Mem.extends m m' ->
  exists v', eval_binop op v1' v2' m' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until m'; intros EV LD1 LD2 ME.
  assert (exists v', eval_binop op v1' v2' m = Some v' /\ Val.lessdef v v').
  inv LD1. inv LD2. exists v; auto. 
  destruct op; destruct v1'; simpl in *; inv EV; TrivialExists.
  destruct op; simpl in *; inv EV; TrivialExists.
  destruct op; try (exact H). 
  simpl in *. TrivialExists. inv EV. apply Val.of_optbool_lessdef. 
  intros. apply Val.cmpu_bool_lessdef with (Mem.valid_pointer m) v1 v2; auto.
  intros; eapply Mem.valid_pointer_extends; eauto.
Qed.

(** * Semantic preservation for instruction selection. *)

(** Relationship between the local environments. *)

Definition env_lessdef (e1 e2: env) : Prop :=
  forall id v1, e1!id = Some v1 -> exists v2, e2!id = Some v2 /\ Val.lessdef v1 v2.

Lemma set_var_lessdef:
  forall e1 e2 id v1 v2,
  env_lessdef e1 e2 -> Val.lessdef v1 v2 ->
  env_lessdef (PTree.set id v1 e1) (PTree.set id v2 e2).
Proof.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
  exists v2; split; congruence.
  auto.
Qed.

Lemma set_params_lessdef:
  forall il vl1 vl2, 
  Val.lessdef_list vl1 vl2 ->
  env_lessdef (set_params vl1 il) (set_params vl2 il).
Proof.
  induction il; simpl; intros.
  red; intros. rewrite PTree.gempty in H0; congruence.
  inv H; apply set_var_lessdef; auto.
Qed.

Lemma set_locals_lessdef:
  forall e1 e2, env_lessdef e1 e2 ->
  forall il, env_lessdef (set_locals il e1) (set_locals il e2).
Proof.
  induction il; simpl. auto. apply set_var_lessdef; auto.
Qed.

(** Semantic preservation for expressions. *)

Lemma sel_expr_correct:
  forall sp e m a v,
  Cminor.eval_expr ge sp e m a v ->
  forall e' le m',
  env_lessdef e e' -> Mem.extends m m' ->
  exists v', eval_expr tge sp e' m' le (sel_expr hf a) v' /\ Val.lessdef v v'.
Proof.
  induction 1; intros; simpl.
  (* Evar *)
  exploit H0; eauto. intros [v' [A B]]. exists v'; split; auto. constructor; auto.
  (* Econst *)
  destruct cst; simpl in *; inv H. 
  exists (Vint i); split; auto. econstructor. constructor. auto. 
  exists (Vfloat f); split; auto. econstructor. constructor. auto.
  exists (Val.longofwords (Vint (Int64.hiword i)) (Vint (Int64.loword i))); split.
  eapply eval_Eop. constructor. EvalOp. simpl; eauto. constructor. EvalOp. simpl; eauto. constructor. auto.
  simpl. rewrite Int64.ofwords_recompose. auto.
  rewrite <- symbols_preserved. fold (symbol_address tge i i0). apply eval_addrsymbol.
  apply eval_addrstack.
  (* Eunop *)
  exploit IHeval_expr; eauto. intros [v1' [A B]].
  exploit eval_unop_lessdef; eauto. intros [v' [C D]].
  exploit eval_sel_unop; eauto. intros [v'' [E F]].
  exists v''; split; eauto. eapply Val.lessdef_trans; eauto. 
  (* Ebinop *)
  exploit IHeval_expr1; eauto. intros [v1' [A B]].
  exploit IHeval_expr2; eauto. intros [v2' [C D]].
  exploit eval_binop_lessdef; eauto. intros [v' [E F]].
  exploit eval_sel_binop. eexact A. eexact C. eauto. intros [v'' [P Q]].
  exists v''; split; eauto. eapply Val.lessdef_trans; eauto. 
  (* Eload *)
  exploit IHeval_expr; eauto. intros [vaddr' [A B]].
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  exists v'; split; auto. eapply eval_load; eauto.
Qed.

Lemma sel_exprlist_correct:
  forall sp e m a v,
  Cminor.eval_exprlist ge sp e m a v ->
  forall e' le m',
  env_lessdef e e' -> Mem.extends m m' ->
  exists v', eval_exprlist tge sp e' m' le (sel_exprlist hf a) v' /\ Val.lessdef_list v v'.
Proof.
  induction 1; intros; simpl. 
  exists (@nil val); split; auto. constructor.
  exploit sel_expr_correct; eauto. intros [v1' [A B]].
  exploit IHeval_exprlist; eauto. intros [vl' [C D]].
  exists (v1' :: vl'); split; auto. constructor; eauto.
Qed.

(** Semantic preservation for functions and statements. *)

Inductive match_cont: Cminor.cont -> CminorSel.cont -> Prop :=
  | match_cont_stop:
      match_cont Cminor.Kstop Kstop
  | match_cont_seq: forall s k k',
      match_cont k k' ->
      match_cont (Cminor.Kseq s k) (Kseq (sel_stmt hf ge s) k')
  | match_cont_block: forall k k',
      match_cont k k' ->
      match_cont (Cminor.Kblock k) (Kblock k')
  | match_cont_call: forall id f sp e k e' k',
      match_cont k k' -> env_lessdef e e' ->
      match_cont (Cminor.Kcall id f sp e k) (Kcall id (sel_function hf ge f) sp e' k').

Inductive match_states: Cminor.state -> CminorSel.state -> Prop :=
  | match_state: forall f s k s' k' sp e m e' m',
      s' = sel_stmt hf ge s ->
      match_cont k k' ->
      env_lessdef e e' ->
      Mem.extends m m' ->
      match_states
        (Cminor.State f s k sp e m)
        (State (sel_function hf ge f) s' k' sp e' m')
  | match_callstate: forall f args args' k k' m m',
      match_cont k k' ->
      Val.lessdef_list args args' ->
      Mem.extends m m' ->
      match_states
        (Cminor.Callstate f args k m)
        (Callstate (sel_fundef hf ge f) args' k' m')
  | match_returnstate: forall v v' k k' m m',
      match_cont k k' ->
      Val.lessdef v v' ->
      Mem.extends m m' ->
      match_states
        (Cminor.Returnstate v k m)
        (Returnstate v' k' m')
  | match_builtin_1: forall ef args args' optid f sp e k m al e' k' m',
      match_cont k k' ->
      Val.lessdef_list args args' ->
      env_lessdef e e' ->
      Mem.extends m m' ->
      eval_exprlist tge sp e' m' nil al args' ->
      match_states
        (Cminor.Callstate (External ef) args (Cminor.Kcall optid f sp e k) m)
        (State (sel_function hf ge f) (Sbuiltin optid ef al) k' sp e' m')
  | match_builtin_2: forall v v' optid f sp e k m e' m' k',
      match_cont k k' ->
      Val.lessdef v v' ->
      env_lessdef e e' ->
      Mem.extends m m' ->
      match_states
        (Cminor.Returnstate v (Cminor.Kcall optid f sp e k) m)
        (State (sel_function hf ge f) Sskip k' sp (set_optvar optid v' e') m').

Remark call_cont_commut:
  forall k k', match_cont k k' -> match_cont (Cminor.call_cont k) (call_cont k').
Proof.
  induction 1; simpl; auto. constructor. constructor; auto.
Qed.

Remark find_label_commut:
  forall lbl s k k',
  match_cont k k' ->
  match Cminor.find_label lbl s k, find_label lbl (sel_stmt hf ge s) k' with
  | None, None => True
  | Some(s1, k1), Some(s1', k1') => s1' = sel_stmt hf ge s1 /\ match_cont k1 k1'
  | _, _ => False
  end.
Proof.
  induction s; intros; simpl; auto.
(* store *)
  unfold store. destruct (addressing m (sel_expr hf e)); simpl; auto.
(* call *)
  destruct (classify_call ge e); simpl; auto.
(* tailcall *)
  destruct (classify_call ge e); simpl; auto.
(* seq *)
  exploit (IHs1 (Cminor.Kseq s2 k)). constructor; eauto. 
  destruct (Cminor.find_label lbl s1 (Cminor.Kseq s2 k)) as [[sx kx] | ];
  destruct (find_label lbl (sel_stmt hf ge s1) (Kseq (sel_stmt hf ge s2) k')) as [[sy ky] | ];
  intuition. apply IHs2; auto.
(* ifthenelse *)
  exploit (IHs1 k); eauto. 
  destruct (Cminor.find_label lbl s1 k) as [[sx kx] | ];
  destruct (find_label lbl (sel_stmt hf ge s1) k') as [[sy ky] | ];
  intuition. apply IHs2; auto.
(* loop *)
  apply IHs. constructor; auto.
(* block *)
  apply IHs. constructor; auto.
(* return *)
  destruct o; simpl; auto. 
(* label *)
  destruct (ident_eq lbl l). auto. apply IHs; auto.
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
  induction 1; intros T1 ME; inv ME; simpl.
  (* skip seq *)
  inv H7. left; econstructor; split. econstructor. constructor; auto.
  (* skip block *)
  inv H7. left; econstructor; split. econstructor. constructor; auto.
  (* skip call *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  left; econstructor; split. 
  econstructor. inv H9; simpl in H; simpl; auto. 
  eauto. 
  constructor; auto.
  (* assign *)
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split.
  econstructor; eauto.
  constructor; auto. apply set_var_lessdef; auto.
  (* store *)
  exploit sel_expr_correct. eexact H. eauto. eauto. intros [vaddr' [A B]].
  exploit sel_expr_correct. eexact H0. eauto. eauto. intros [v' [C D]].
  exploit Mem.storev_extends; eauto. intros [m2' [P Q]].
  left; econstructor; split.
  eapply eval_store; eauto.
  constructor; auto.
  (* Scall *)
  exploit sel_exprlist_correct; eauto. intros [vargs' [C D]].
  exploit classify_call_correct; eauto. 
  destruct (classify_call ge a) as [ | id | ef].
  (* indirect *)
  exploit sel_expr_correct; eauto. intros [vf' [A B]].
  left; econstructor; split.
  econstructor; eauto. econstructor; eauto. 
  eapply functions_translated; eauto. 
  apply sig_function_translated.
  constructor; auto. constructor; auto.
  (* direct *)
  intros [b [U V]]. 
  left; econstructor; split.
  econstructor; eauto. econstructor; eauto. rewrite symbols_preserved; eauto.
  eapply functions_translated; eauto. subst vf; auto. 
  apply sig_function_translated.
  constructor; auto. constructor; auto.
  (* turned into Sbuiltin *)
  intros EQ. subst fd. 
  right; split. omega. split. auto. 
  econstructor; eauto.
  (* Stailcall *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  exploit sel_expr_correct; eauto. intros [vf' [A B]].
  exploit sel_exprlist_correct; eauto. intros [vargs' [C D]].
  left; econstructor; split.
  exploit classify_call_correct; eauto. 
  destruct (classify_call ge a) as [ | id | ef]; intros. 
  econstructor; eauto. econstructor; eauto. eapply functions_translated; eauto. apply sig_function_translated.
  destruct H2 as [b [U V]].
  econstructor; eauto. econstructor; eauto. rewrite symbols_preserved; eauto. eapply functions_translated; eauto. subst vf; auto. apply sig_function_translated.
  econstructor; eauto. econstructor; eauto. eapply functions_translated; eauto. apply sig_function_translated.
  constructor; auto. apply call_cont_commut; auto.
  (* Sbuiltin *)
  exploit sel_exprlist_correct; eauto. intros [vargs' [P Q]].
  exploit external_call_mem_extends; eauto. 
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  econstructor. eauto. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.
  destruct optid; simpl; auto. apply set_var_lessdef; auto.
  (* Seq *)
  left; econstructor; split. constructor. constructor; auto. constructor; auto.
  (* Sifthenelse *)
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  assert (Val.bool_of_val v' b). inv B. auto. inv H0.
  left; exists (State (sel_function hf ge f) (if b then sel_stmt hf ge s1 else sel_stmt hf ge s2) k' sp e' m'); split.
  econstructor; eauto. eapply eval_condexpr_of_expr; eauto. 
  constructor; auto. destruct b; auto.
  (* Sloop *)
  left; econstructor; split. constructor. constructor; auto. constructor; auto.
  (* Sblock *)
  left; econstructor; split. constructor. constructor; auto. constructor; auto.
  (* Sexit seq *)
  inv H7. left; econstructor; split. constructor. constructor; auto.
  (* Sexit0 block *)
  inv H7. left; econstructor; split. constructor. constructor; auto.
  (* SexitS block *)
  inv H7. left; econstructor; split. constructor. constructor; auto.
  (* Sswitch *)
  exploit sel_expr_correct; eauto. intros [v' [A B]]. inv B.
  left; econstructor; split. econstructor; eauto. constructor; auto.
  (* Sreturn None *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  left; econstructor; split. 
  econstructor. simpl; eauto. 
  constructor; auto. apply call_cont_commut; auto.
  (* Sreturn Some *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split. 
  econstructor; eauto.
  constructor; auto. apply call_cont_commut; auto.
  (* Slabel *)
  left; econstructor; split. constructor. constructor; auto.
  (* Sgoto *)
  exploit (find_label_commut lbl (Cminor.fn_body f) (Cminor.call_cont k)).
    apply call_cont_commut; eauto.
  rewrite H. 
  destruct (find_label lbl (sel_stmt hf ge (Cminor.fn_body f)) (call_cont k'0))
  as [[s'' k'']|] eqn:?; intros; try contradiction.
  destruct H0. 
  left; econstructor; split.
  econstructor; eauto. 
  constructor; auto.
  (* internal function *)
  exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl. 
  intros [m2' [A B]].
  left; econstructor; split.
  econstructor; eauto.
  constructor; auto. apply set_locals_lessdef. apply set_params_lessdef; auto.
  (* external call *)
  exploit external_call_mem_extends; eauto. 
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  econstructor. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.
  (* external call turned into a Sbuiltin *)
  exploit external_call_mem_extends; eauto. 
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  econstructor. eauto. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.
  (* return *)
  inv H2. 
  left; econstructor; split. 
  econstructor. 
  constructor; auto. destruct optid; simpl; auto. apply set_var_lessdef; auto.
  (* return of an external call turned into a Sbuiltin *)
  right; split. omega. split. auto. constructor; auto. 
  destruct optid; simpl; auto. apply set_var_lessdef; auto.
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
  constructor; auto. constructor. apply Mem.extends_refl.
Qed.

Lemma sel_final_states:
  forall S R r,
  match_states S R -> Cminor.final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H. inv H3. inv H5. constructor.
Qed.

End PRESERVATION.

Axiom get_helpers_correct:
  forall ge hf, get_helpers ge = OK hf -> i64_helpers_correct ge hf.

Theorem transf_program_correct:
  forall prog tprog,
  sel_program prog = OK tprog ->
  forward_simulation (Cminor.semantics prog) (CminorSel.semantics tprog).
Proof.
  intros. unfold sel_program in H. 
  destruct (get_helpers (Genv.globalenv prog)) as [hf|] eqn:E; simpl in H; try discriminate.
  inv H.
  eapply forward_simulation_opt.
  apply symbols_preserved.
  apply sel_initial_states.
  apply sel_final_states.
  apply sel_step_correct. apply helpers_correct_preserved. apply get_helpers_correct. auto.
Qed.

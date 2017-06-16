(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** A big-step semantics for the Clight language. *)

Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Clight.

Section BIGSTEP.

Variable ge: genv.

(** ** Big-step semantics for terminating statements and functions *)

(** The execution of a statement produces an ``outcome'', indicating
  how the execution terminated: either normally or prematurely
  through the execution of a [break], [continue] or [return] statement. *)

Inductive outcome: Type :=
   | Out_break: outcome                 (**r terminated by [break] *)
   | Out_continue: outcome              (**r terminated by [continue] *)
   | Out_normal: outcome                (**r terminated normally *)
   | Out_return: option (val * type) -> outcome. (**r terminated by [return] *)

Inductive out_normal_or_continue : outcome -> Prop :=
  | Out_normal_or_continue_N: out_normal_or_continue Out_normal
  | Out_normal_or_continue_C: out_normal_or_continue Out_continue.

Inductive out_break_or_return : outcome -> outcome -> Prop :=
  | Out_break_or_return_B: out_break_or_return Out_break Out_normal
  | Out_break_or_return_R: forall ov,
      out_break_or_return (Out_return ov) (Out_return ov).

Definition outcome_switch (out: outcome) : outcome :=
  match out with
  | Out_break => Out_normal
  | o => o
  end.

Definition outcome_result_value (out: outcome) (t: type) (v: val) (m: mem): Prop :=
  match out, t with
  | Out_normal, Tvoid => v = Vundef
  | Out_return None, Tvoid => v = Vundef
  | Out_return (Some (v',t')), ty => ty <> Tvoid /\ sem_cast v' t' t m = Some v
  | _, _ => False
  end.

(** [exec_stmt ge e m1 s t m2 out] describes the execution of
  the statement [s].  [out] is the outcome for this execution.
  [m1] is the initial memory state, [m2] the final memory state.
  [t] is the trace of input/output events performed during this
  evaluation. *)

Inductive exec_stmt: env -> temp_env -> mem -> statement -> trace -> temp_env -> mem -> outcome -> Prop :=
  | exec_Sskip:   forall e le m,
      exec_stmt e le m Sskip
               E0 le m Out_normal
  | exec_Sassign:   forall e le m a1 a2 loc ofs v2 v m',
      eval_lvalue ge e le m a1 loc ofs ->
      eval_expr ge e le m a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_loc ge (typeof a1) m loc ofs v m' ->
      exec_stmt e le m (Sassign a1 a2)
               E0 le m' Out_normal
  | exec_Sset:     forall e le m id a v,
      eval_expr ge e le m a v ->
      exec_stmt e le m (Sset id a)
               E0 (PTree.set id v le) m Out_normal
  | exec_Scall:   forall e le m optid a al tyargs tyres cconv vf vargs f t m' vres,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr ge e le m a vf ->
      eval_exprlist ge e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some f ->
      type_of_fundef f = Tfunction tyargs tyres cconv ->
      eval_funcall m f vargs t m' vres ->
      exec_stmt e le m (Scall optid a al)
                t (set_opttemp optid vres le) m' Out_normal
  | exec_Sbuiltin:   forall e le m optid ef al tyargs vargs t m' vres,
      eval_exprlist ge e le m al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      exec_stmt e le m (Sbuiltin optid ef tyargs al)
                t (set_opttemp optid vres le) m' Out_normal
  | exec_Sseq_1:   forall e le m s1 s2 t1 le1 m1 t2 le2 m2 out,
      exec_stmt e le m s1 t1 le1 m1 Out_normal ->
      exec_stmt e le1 m1 s2 t2 le2 m2 out ->
      exec_stmt e le m (Ssequence s1 s2)
                (t1 ** t2) le2 m2 out
  | exec_Sseq_2:   forall e le m s1 s2 t1 le1 m1 out,
      exec_stmt e le m s1 t1 le1 m1 out ->
      out <> Out_normal ->
      exec_stmt e le m (Ssequence s1 s2)
                t1 le1 m1 out
  | exec_Sifthenelse: forall e le m a s1 s2 v1 b t le' m' out,
      eval_expr ge e le m a v1 ->
      bool_val v1 (typeof a) m = Some b ->
      exec_stmt e le m (if b then s1 else s2) t le' m' out ->
      exec_stmt e le m (Sifthenelse a s1 s2)
                t le' m' out
  | exec_Sreturn_none:   forall e le m,
      exec_stmt e le m (Sreturn None)
               E0 le m (Out_return None)
  | exec_Sreturn_some: forall e le m a v,
      eval_expr ge e le m a v ->
      exec_stmt e le m (Sreturn (Some a))
                E0 le m (Out_return (Some (v, typeof a)))
  | exec_Sbreak:   forall e le m,
      exec_stmt e le m Sbreak
               E0 le m Out_break
  | exec_Scontinue:   forall e le m,
      exec_stmt e le m Scontinue
               E0 le m Out_continue
  | exec_Sloop_stop1: forall e le m s1 s2 t le' m' out' out,
      exec_stmt e le m s1 t le' m' out' ->
      out_break_or_return out' out ->
      exec_stmt e le m (Sloop s1 s2)
                t le' m' out
  | exec_Sloop_stop2: forall e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 out2 out,
      exec_stmt e le m s1 t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e le1 m1 s2 t2 le2 m2 out2 ->
      out_break_or_return out2 out ->
      exec_stmt e le m (Sloop s1 s2)
                (t1**t2) le2 m2 out
  | exec_Sloop_loop: forall e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 t3 le3 m3 out,
      exec_stmt e le m s1 t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e le1 m1 s2 t2 le2 m2 Out_normal ->
      exec_stmt e le2 m2 (Sloop s1 s2) t3 le3 m3 out ->
      exec_stmt e le m (Sloop s1 s2)
                (t1**t2**t3) le3 m3 out
  | exec_Sswitch:   forall e le m a t v n sl le1 m1 out,
      eval_expr ge e le m a v ->
      sem_switch_arg v (typeof a) = Some n ->
      exec_stmt e le m (seq_of_labeled_statement (select_switch n sl)) t le1 m1 out ->
      exec_stmt e le m (Sswitch a sl)
                t le1 m1 (outcome_switch out)

(** [eval_funcall m1 fd args t m2 res] describes the invocation of
  function [fd] with arguments [args].  [res] is the value returned
  by the call.  *)

with eval_funcall: mem -> fundef -> list val -> trace -> mem -> val -> Prop :=
  | eval_funcall_internal: forall le m f vargs t e m1 m2 m3 out vres m4,
      alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      bind_parameters ge e m1 f.(fn_params) vargs m2 ->
      exec_stmt e (create_undef_temps f.(fn_temps)) m2 f.(fn_body) t le m3 out ->
      outcome_result_value out f.(fn_return) vres m3 ->
      Mem.free_list m3 (blocks_of_env ge e) = Some m4 ->
      eval_funcall m (Internal f) vargs t m4 vres
  | eval_funcall_external: forall m ef targs tres cconv vargs t vres m',
      external_call ef ge vargs m t vres m' ->
      eval_funcall m (External ef targs tres cconv) vargs t m' vres.

Scheme exec_stmt_ind2 := Minimality for exec_stmt Sort Prop
  with eval_funcall_ind2 := Minimality for eval_funcall Sort Prop.
Combined Scheme exec_stmt_funcall_ind from exec_stmt_ind2, eval_funcall_ind2.

(** ** Big-step semantics for diverging statements and functions *)

(** Coinductive semantics for divergence.
  [execinf_stmt ge e m s t] holds if the execution of statement [s]
  diverges, i.e. loops infinitely.  [t] is the possibly infinite
  trace of observable events performed during the execution. *)

CoInductive execinf_stmt: env -> temp_env -> mem -> statement -> traceinf -> Prop :=
  | execinf_Scall:   forall e le m optid a al vf tyargs tyres cconv vargs f t,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr ge e le m a vf ->
      eval_exprlist ge e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some f ->
      type_of_fundef f = Tfunction tyargs tyres cconv ->
      evalinf_funcall m f vargs t ->
      execinf_stmt e le m (Scall optid a al) t
  | execinf_Sseq_1:   forall e le m s1 s2 t,
      execinf_stmt e le m s1 t ->
      execinf_stmt e le m (Ssequence s1 s2) t
  | execinf_Sseq_2:   forall e le m s1 s2 t1 le1 m1 t2,
      exec_stmt e le m s1 t1 le1 m1 Out_normal ->
      execinf_stmt e le1 m1 s2 t2 ->
      execinf_stmt e le m (Ssequence s1 s2) (t1 *** t2)
  | execinf_Sifthenelse: forall e le m a s1 s2 v1 b t,
      eval_expr ge e le m a v1 ->
      bool_val v1 (typeof a) m = Some b ->
      execinf_stmt e le m (if b then s1 else s2) t ->
      execinf_stmt e le m (Sifthenelse a s1 s2) t
  | execinf_Sloop_body1: forall e le m s1 s2 t,
      execinf_stmt e le m s1 t ->
      execinf_stmt e le m (Sloop s1 s2) t
  | execinf_Sloop_body2: forall e le m s1 s2 t1 le1 m1 out1 t2,
      exec_stmt e le m s1 t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      execinf_stmt e le1 m1 s2 t2 ->
      execinf_stmt e le m (Sloop s1 s2) (t1***t2)
  | execinf_Sloop_loop: forall e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 t3,
      exec_stmt e le m s1 t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e le1 m1 s2 t2 le2 m2 Out_normal ->
      execinf_stmt e le2 m2 (Sloop s1 s2) t3 ->
      execinf_stmt e le m (Sloop s1 s2) (t1***t2***t3)
  | execinf_Sswitch:   forall e le m a t v n sl,
      eval_expr ge e le m a v ->
      sem_switch_arg v (typeof a) = Some n ->
      execinf_stmt e le m (seq_of_labeled_statement (select_switch n sl)) t ->
      execinf_stmt e le m (Sswitch a sl) t

(** [evalinf_funcall ge m fd args t] holds if the invocation of function
    [fd] on arguments [args] diverges, with observable trace [t]. *)

with evalinf_funcall: mem -> fundef -> list val -> traceinf -> Prop :=
  | evalinf_funcall_internal: forall m f vargs t e m1 m2,
      alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      bind_parameters ge e m1 f.(fn_params) vargs m2 ->
      execinf_stmt e (create_undef_temps f.(fn_temps)) m2 f.(fn_body) t ->
      evalinf_funcall m (Internal f) vargs t.

End BIGSTEP.

(** Big-step execution of a whole program.  *)

Inductive bigstep_program_terminates (p: program): trace -> int -> Prop :=
  | bigstep_program_terminates_intro: forall b f m0 m1 t r,
      let ge := globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      eval_funcall ge m0 f nil t m1 (Vint r) ->
      bigstep_program_terminates p t r.

Inductive bigstep_program_diverges (p: program): traceinf -> Prop :=
  | bigstep_program_diverges_intro: forall b f m0 t,
      let ge := globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      evalinf_funcall ge m0 f nil t ->
      bigstep_program_diverges p t.

Definition bigstep_semantics (p: program) :=
  Bigstep_semantics (bigstep_program_terminates p) (bigstep_program_diverges p).

(** * Implication from big-step semantics to transition semantics *)

Section BIGSTEP_TO_TRANSITIONS.

Variable prog: program.
Let ge : genv := globalenv prog.

Inductive outcome_state_match
       (e: env) (le: temp_env) (m: mem) (f: function) (k: cont): outcome -> state -> Prop :=
  | osm_normal:
      outcome_state_match e le m f k Out_normal (State f Sskip k e le m)
  | osm_break:
      outcome_state_match e le m f k Out_break (State f Sbreak k e le m)
  | osm_continue:
      outcome_state_match e le m f k Out_continue (State f Scontinue k e le m)
  | osm_return_none: forall k',
      call_cont k' = call_cont k ->
      outcome_state_match e le m f k
        (Out_return None) (State f (Sreturn None) k' e le m)
  | osm_return_some: forall a v k',
      call_cont k' = call_cont k ->
      eval_expr ge e le m a v ->
      outcome_state_match e le m f k
        (Out_return (Some (v,typeof a))) (State f (Sreturn (Some a)) k' e le m).

Lemma is_call_cont_call_cont:
  forall k, is_call_cont k -> call_cont k = k.
Proof.
  destruct k; simpl; intros; contradiction || auto.
Qed.

Lemma exec_stmt_eval_funcall_steps:
  (forall e le m s t le' m' out,
   exec_stmt ge e le m s t le' m' out ->
   forall f k, exists S,
   star step1 ge (State f s k e le m) t S
   /\ outcome_state_match e le' m' f k out S)
/\
  (forall m fd args t m' res,
   eval_funcall ge m fd args t m' res ->
   forall k,
   is_call_cont k ->
   star step1 ge (Callstate fd args k m) t (Returnstate res k m')).
Proof.
  apply exec_stmt_funcall_ind; intros.

(* skip *)
  econstructor; split. apply star_refl. constructor.

(* assign *)
  econstructor; split. apply star_one. econstructor; eauto. constructor.

(* set *)
  econstructor; split. apply star_one. econstructor; eauto. constructor.

(* call *)
  econstructor; split.
  eapply star_left. econstructor; eauto.
  eapply star_right. apply H5. simpl; auto. econstructor. reflexivity. traceEq.
  constructor.

(* builtin *)
  econstructor; split. apply star_one. econstructor; eauto. constructor.

(* sequence 2 *)
  destruct (H0 f (Kseq s2 k)) as [S1 [A1 B1]]. inv B1.
  destruct (H2 f k) as [S2 [A2 B2]].
  econstructor; split.
  eapply star_left. econstructor.
  eapply star_trans. eexact A1.
  eapply star_left. constructor. eexact A2.
  reflexivity. reflexivity. traceEq.
  auto.

(* sequence 1 *)
  destruct (H0 f (Kseq s2 k)) as [S1 [A1 B1]].
  set (S2 :=
    match out with
    | Out_break => State f Sbreak k e le1 m1
    | Out_continue => State f Scontinue k e le1 m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. econstructor.
  eapply star_trans. eexact A1.
  unfold S2; inv B1.
    congruence.
    apply star_one. apply step_break_seq.
    apply star_one. apply step_continue_seq.
    apply star_refl.
    apply star_refl.
  reflexivity. traceEq.
  unfold S2; inv B1; congruence || econstructor; eauto.

(* ifthenelse *)
  destruct (H2 f k) as [S1 [A1 B1]].
  exists S1; split.
  eapply star_left. 2: eexact A1. eapply step_ifthenelse; eauto. traceEq.
  auto.

(* return none *)
  econstructor; split. apply star_refl. constructor. auto.

(* return some *)
  econstructor; split. apply star_refl. econstructor; eauto.

(* break *)
  econstructor; split. apply star_refl. constructor.

(* continue *)
  econstructor; split. apply star_refl. constructor.

(* loop stop 1 *)
  destruct (H0 f (Kloop1 s1 s2 k)) as [S1 [A1 B1]].
  set (S2 :=
    match out' with
    | Out_break => State f Sskip k e le' m'
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. eapply step_loop.
  eapply star_trans. eexact A1.
  unfold S2. inversion H1; subst.
  inv B1. apply star_one. constructor.
  apply star_refl.
  reflexivity. traceEq.
  unfold S2. inversion H1; subst. constructor. inv B1; econstructor; eauto.

(* loop stop 2 *)
  destruct (H0 f (Kloop1 s1 s2 k)) as [S1 [A1 B1]].
  destruct (H3 f (Kloop2 s1 s2 k)) as [S2 [A2 B2]].
  set (S3 :=
    match out2 with
    | Out_break => State f Sskip k e le2 m2
    | _ => S2
    end).
  exists S3; split.
  eapply star_left. eapply step_loop.
  eapply star_trans. eexact A1.
  eapply star_left with (s2 := State f s2 (Kloop2 s1 s2 k) e le1 m1).
  inv H1; inv B1; constructor; auto.
  eapply star_trans. eexact A2.
  unfold S3. inversion H4; subst.
  inv B2. apply star_one. constructor. apply star_refl.
  reflexivity. reflexivity. reflexivity. traceEq.
  unfold S3. inversion H4; subst. constructor. inv B2; econstructor; eauto.

(* loop loop *)
  destruct (H0 f (Kloop1 s1 s2 k)) as [S1 [A1 B1]].
  destruct (H3 f (Kloop2 s1 s2 k)) as [S2 [A2 B2]].
  destruct (H5 f k) as [S3 [A3 B3]].
  exists S3; split.
  eapply star_left. eapply step_loop.
  eapply star_trans. eexact A1.
  eapply star_left with (s2 := State f s2 (Kloop2 s1 s2 k) e le1 m1).
  inv H1; inv B1; constructor; auto.
  eapply star_trans. eexact A2.
  eapply star_left with (s2 := State f (Sloop s1 s2) k e le2 m2).
  inversion H4; subst; inv B2; constructor; auto.
  eexact A3.
  reflexivity. reflexivity. reflexivity. reflexivity. traceEq.
  auto.

(* switch *)
  destruct (H2 f (Kswitch k)) as [S1 [A1 B1]].
  set (S2 :=
    match out with
    | Out_normal => State f Sskip k e le1 m1
    | Out_break => State f Sskip k e le1 m1
    | Out_continue => State f Scontinue k e le1 m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. eapply step_switch; eauto.
  eapply star_trans. eexact A1.
  unfold S2; inv B1.
    apply star_one. constructor. auto.
    apply star_one. constructor. auto.
    apply star_one. constructor.
    apply star_refl.
    apply star_refl.
  reflexivity. traceEq.
  unfold S2. inv B1; simpl; econstructor; eauto.

(* call internal *)
  destruct (H3 f k) as [S1 [A1 B1]].
  eapply star_left. eapply step_internal_function; eauto. econstructor; eauto.
  eapply star_right. eexact A1.
   inv B1; simpl in H4; try contradiction.
  (* Out_normal *)
  assert (fn_return f = Tvoid /\ vres = Vundef).
    destruct (fn_return f); auto || contradiction.
  destruct H7. subst vres. apply step_skip_call; auto.
  (* Out_return None *)
  assert (fn_return f = Tvoid /\ vres = Vundef).
    destruct (fn_return f); auto || contradiction.
  destruct H8. subst vres.
  rewrite <- (is_call_cont_call_cont k H6). rewrite <- H7.
  apply step_return_0; auto.
  (* Out_return Some *)
  destruct H4.
  rewrite <- (is_call_cont_call_cont k H6). rewrite <- H7.
  eapply step_return_1; eauto.
  reflexivity. traceEq.

(* call external *)
  apply star_one. apply step_external_function; auto.
Qed.

Lemma exec_stmt_steps:
   forall e le m s t le' m' out,
   exec_stmt ge e le m s t le' m' out ->
   forall f k, exists S,
   star step1 ge (State f s k e le m) t S
   /\ outcome_state_match e le' m' f k out S.
Proof (proj1 exec_stmt_eval_funcall_steps).

Lemma eval_funcall_steps:
   forall m fd args t m' res,
   eval_funcall ge m fd args t m' res ->
   forall k,
   is_call_cont k ->
   star step1 ge (Callstate fd args k m) t (Returnstate res k m').
Proof (proj2 exec_stmt_eval_funcall_steps).

Definition order (x y: unit) := False.

Lemma evalinf_funcall_forever:
  forall m fd args T k,
  evalinf_funcall ge m fd args T ->
  forever_N step1 order ge tt (Callstate fd args k m) T.
Proof.
  cofix CIH_FUN.
  assert (forall e le m s T f k,
          execinf_stmt ge e le m s T ->
          forever_N step1 order ge tt (State f s k e le m) T).
  cofix CIH_STMT.
  intros. inv H.

(* call  *)
  eapply forever_N_plus.
  apply plus_one. eapply step_call; eauto.
  eapply CIH_FUN. eauto. traceEq.

(* seq 1 *)
  eapply forever_N_plus.
  apply plus_one. econstructor.
  apply CIH_STMT; eauto. traceEq.
(* seq 2 *)
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ H0 f (Kseq s2 k)) as [S1 [A1 B1]].
  inv B1.
  eapply forever_N_plus.
  eapply plus_left. constructor. eapply star_trans. eexact A1.
  apply star_one. constructor. reflexivity. reflexivity.
  apply CIH_STMT; eauto. traceEq.

(* ifthenelse *)
  eapply forever_N_plus.
  apply plus_one. eapply step_ifthenelse with (b := b); eauto.
  apply CIH_STMT; eauto. traceEq.

(* loop body 1 *)
  eapply forever_N_plus.
  eapply plus_one. constructor.
  apply CIH_STMT; eauto. traceEq.
(* loop body 2 *)
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ H0 f (Kloop1 s1 s2 k)) as [S1 [A1 B1]].
  eapply forever_N_plus with (s2 := State f s2 (Kloop2 s1 s2 k) e le1 m1).
  eapply plus_left. constructor.
  eapply star_right. eexact A1.
  inv H1; inv B1; constructor; auto.
  reflexivity. reflexivity.
  apply CIH_STMT; eauto. traceEq.
(* loop loop *)
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ H0 f (Kloop1 s1 s2 k)) as [S1 [A1 B1]].
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ H2 f (Kloop2 s1 s2 k)) as [S2 [A2 B2]].
  eapply forever_N_plus with (s2 := State f (Sloop s1 s2) k e le2 m2).
  eapply plus_left. constructor.
  eapply star_trans. eexact A1.
  eapply star_left. inv H1; inv B1; constructor; auto.
  eapply star_right. eexact A2.
  inv B2. constructor.
  reflexivity. reflexivity. reflexivity. reflexivity.
  apply CIH_STMT; eauto. traceEq.

(* switch *)
  eapply forever_N_plus.
  eapply plus_one. eapply step_switch; eauto.
  apply CIH_STMT; eauto.
  traceEq.

(* call internal *)
  intros. inv H0.
  eapply forever_N_plus.
  eapply plus_one. econstructor; eauto. econstructor; eauto.
  apply H; eauto.
  traceEq.
Qed.

Theorem bigstep_semantics_sound:
  bigstep_sound (bigstep_semantics prog) (semantics1 prog).
Proof.
  constructor; simpl; intros.
(* termination *)
  inv H. econstructor; econstructor.
  split. econstructor; eauto.
  split. eapply eval_funcall_steps. eauto. red; auto.
  econstructor.
(* divergence *)
  inv H. econstructor.
  split. econstructor; eauto.
  eapply forever_N_forever with (order := order).
  red; intros. constructor; intros. red in H. elim H.
  eapply evalinf_funcall_forever; eauto.
Qed.

End BIGSTEP_TO_TRANSITIONS.

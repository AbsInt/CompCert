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

(** Correctness proof for cast optimization. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Lattice.
Require Import Kildall.
Require Import CastOptim.

(** * Correctness of the static analysis *)

Section ANALYSIS.

Definition val_match_approx (a: approx) (v: val) : Prop :=
  match a with
  | Novalue => False
  | Int7 => v = Val.zero_ext 8 v /\ v = Val.sign_ext 8 v
  | Int8u => v = Val.zero_ext 8 v
  | Int8s => v = Val.sign_ext 8 v
  | Int15 => v = Val.zero_ext 16 v /\ v = Val.sign_ext 16 v
  | Int16u => v = Val.zero_ext 16 v
  | Int16s => v = Val.sign_ext 16 v
  | Single => v = Val.singleoffloat v
  | Unknown => True
  end.

Definition regs_match_approx (a: D.t) (rs: regset) : Prop :=
  forall r, val_match_approx (D.get r a) rs#r.

Lemma regs_match_approx_top:
  forall rs, regs_match_approx D.top rs.
Proof.
  intros. red; intros. simpl. rewrite PTree.gempty. 
  unfold Approx.top, val_match_approx. auto.
Qed.

Lemma val_match_approx_increasing:
  forall a1 a2 v,
  Approx.ge a1 a2 -> val_match_approx a2 v -> val_match_approx a1 v.
Proof.
  assert (A: forall v, v = Val.zero_ext 8 v -> v = Val.zero_ext 16 v).
    intros. rewrite H.
    destruct v; simpl; auto. decEq. symmetry. 
    apply Int.zero_ext_widen. compute; auto. split. omega. compute; auto.
  assert (B: forall v, v = Val.sign_ext 8 v -> v = Val.sign_ext 16 v).
    intros. rewrite H.
    destruct v; simpl; auto. decEq. symmetry. 
    apply Int.sign_ext_widen. compute; auto. split. omega. compute; auto.
  assert (C: forall v, v = Val.zero_ext 8 v -> v = Val.sign_ext 16 v).
    intros. rewrite H.
    destruct v; simpl; auto. decEq. symmetry. 
    apply Int.sign_zero_ext_widen. compute; auto. split. omega. compute; auto.
  intros. destruct a1; destruct a2; simpl in *; intuition; auto.
Qed.

Lemma regs_match_approx_increasing:
  forall a1 a2 rs,
  D.ge a1 a2 -> regs_match_approx a2 rs -> regs_match_approx a1 rs.
Proof.
  unfold D.ge, regs_match_approx. intros.
  apply val_match_approx_increasing with (D.get r a2); auto.
Qed.

Lemma regs_match_approx_update:
  forall ra rs a v r,
  val_match_approx a v ->
  regs_match_approx ra rs ->
  regs_match_approx (D.set r a ra) (rs#r <- v).
Proof.
  intros; red; intros. rewrite Regmap.gsspec. 
  case (peq r0 r); intro.
  subst r0. rewrite D.gss. auto.
  rewrite D.gso; auto. 
Qed.

Lemma approx_regs_val_list:
  forall ra rs rl,
  regs_match_approx ra rs ->
  list_forall2 val_match_approx (approx_regs ra rl) rs##rl.
Proof.
  induction rl; simpl; intros.
  constructor.
  constructor. apply H. auto.
Qed.

Lemma analyze_correct:
  forall f pc rs pc' i,
  f.(fn_code)!pc = Some i ->
  In pc' (successors_instr i) ->
  regs_match_approx (transfer f pc (analyze f)!!pc) rs ->
  regs_match_approx (analyze f)!!pc' rs.
Proof.
  intros until i. unfold analyze. 
  caseEq (DS.fixpoint (successors f) (transfer f)
                      ((fn_entrypoint f, D.top) :: nil)).
  intros approxs; intros.
  apply regs_match_approx_increasing with (transfer f pc approxs!!pc).
  eapply DS.fixpoint_solution; eauto.
  unfold successors_list, successors. rewrite PTree.gmap. rewrite H0. auto.
  auto.
  intros. rewrite PMap.gi. apply regs_match_approx_top. 
Qed.

Lemma analyze_correct_start:
  forall f rs,
  regs_match_approx (analyze f)!!(f.(fn_entrypoint)) rs.
Proof.
  intros. unfold analyze. 
  caseEq (DS.fixpoint (successors f) (transfer f)
                      ((fn_entrypoint f, D.top) :: nil)).
  intros approxs; intros.
  apply regs_match_approx_increasing with D.top.
  eapply DS.fixpoint_entry; eauto. auto with coqlib.
  apply regs_match_approx_top. 
  intros. rewrite PMap.gi. apply regs_match_approx_top.
Qed.

Lemma approx_bitwise_correct:
  forall (sem_op: int -> int -> int) a1 n1 a2 n2,
  (forall a b c, sem_op (Int.and a c) (Int.and b c) = Int.and (sem_op a b) c) ->
  val_match_approx a1 (Vint n1) -> val_match_approx a2 (Vint n2) ->
  val_match_approx (approx_bitwise_op a1 a2) (Vint (sem_op n1 n2)).
Proof.
  intros.
  assert (forall N, 0 < N < Z_of_nat Int.wordsize ->
    sem_op (Int.zero_ext N n1) (Int.zero_ext N n2) =
    Int.zero_ext N (sem_op (Int.zero_ext N n1) (Int.zero_ext N n2))).
  intros. repeat rewrite Int.zero_ext_and; auto. rewrite H. 
  rewrite Int.and_assoc. rewrite Int.and_idem. auto.
  unfold approx_bitwise_op. 
  caseEq (Approx.bge Int8u a1 && Approx.bge Int8u a2); intro EQ1.
  destruct (andb_prop _ _ EQ1).
  assert (V1: val_match_approx Int8u (Vint n1)).
    eapply val_match_approx_increasing; eauto. apply Approx.bge_correct; eauto.
  assert (V2: val_match_approx Int8u (Vint n2)).
    eapply val_match_approx_increasing; eauto. apply Approx.bge_correct; eauto.
  simpl in *. inversion V1; inversion V2; decEq. apply H2. compute; auto.
  caseEq (Approx.bge Int16u a1 && Approx.bge Int16u a2); intro EQ2.
  destruct (andb_prop _ _ EQ2).
  assert (V1: val_match_approx Int16u (Vint n1)).
    eapply val_match_approx_increasing; eauto. apply Approx.bge_correct; eauto.
  assert (V2: val_match_approx Int16u (Vint n2)).
    eapply val_match_approx_increasing; eauto. apply Approx.bge_correct; eauto.
  simpl in *. inversion V1; inversion V2; decEq. apply H2. compute; auto.
  exact I.
Qed.

Lemma approx_operation_correct:
  forall app rs (ge: genv) sp op args v,
  regs_match_approx app rs ->
  eval_operation ge sp op rs##args = Some v ->
  val_match_approx (approx_operation op (approx_regs app args)) v.
Proof.
  intros. destruct op; simpl; try (exact I). 
(* move *)
  destruct args; try (exact I). destruct args; try (exact I). 
  simpl. simpl in H0. inv H0. apply H. 
(* const int *)
  destruct args; simpl in H0; inv H0.
  destruct (Int.eq_dec i (Int.zero_ext 7 i)). red; simpl.
    split.
    decEq. rewrite e. symmetry. apply Int.zero_ext_widen. compute; auto. split. omega. compute; auto.
    decEq. rewrite e. symmetry. apply Int.sign_zero_ext_widen. compute; auto. compute; auto. 
  destruct (Int.eq_dec i (Int.zero_ext 8 i)). red; simpl; congruence.
  destruct (Int.eq_dec i (Int.sign_ext 8 i)). red; simpl; congruence.
  destruct (Int.eq_dec i (Int.zero_ext 15 i)). red; simpl.
    split.
    decEq. rewrite e. symmetry. apply Int.zero_ext_widen. compute; auto. split. omega. compute; auto.
    decEq. rewrite e. symmetry. apply Int.sign_zero_ext_widen. compute; auto. compute; auto. 
  destruct (Int.eq_dec i (Int.zero_ext 16 i)). red; simpl; congruence.
  destruct (Int.eq_dec i (Int.sign_ext 16 i)). red; simpl; congruence.
  exact I.
(* const float *)
  destruct args; simpl in H0; inv H0. 
  destruct (Float.eq_dec f (Float.singleoffloat f)). red; simpl; congruence.
  exact I.
(* cast8signed *)
  destruct args; simpl in H0; try congruence.
  destruct args; simpl in H0; try congruence.
  inv H0. destruct (rs#p); simpl; auto.
  decEq. symmetry. apply Int.sign_ext_idem. compute; auto.
(* cast8unsigned *)
  destruct args; simpl in H0; try congruence.
  destruct args; simpl in H0; try congruence.
  inv H0. destruct (rs#p); simpl; auto.
  decEq. symmetry. apply Int.zero_ext_idem. compute; auto.
(* cast16signed *)
  destruct args; simpl in H0; try congruence.
  destruct args; simpl in H0; try congruence.
  inv H0. destruct (rs#p); simpl; auto.
  decEq. symmetry. apply Int.sign_ext_idem. compute; auto.
(* cast16unsigned *)
  destruct args; simpl in H0; try congruence.
  destruct args; simpl in H0; try congruence.
  inv H0. destruct (rs#p); simpl; auto.
  decEq. symmetry. apply Int.zero_ext_idem. compute; auto.
(* and *)
  destruct args; try (exact I).
  destruct args; try (exact I).
  destruct args; try (exact I).
  generalize (H p) (H p0). simpl in *. FuncInv. subst. 
  apply approx_bitwise_correct; auto.
  intros. repeat rewrite Int.and_assoc. decEq. 
  rewrite (Int.and_commut b c). rewrite <- Int.and_assoc. rewrite Int.and_idem. auto.
(* or *)
  destruct args; try (exact I).
  destruct args; try (exact I).
  destruct args; try (exact I).
  generalize (H p) (H p0). simpl in *. FuncInv. subst. 
  apply approx_bitwise_correct; auto.
  intros. rewrite (Int.and_commut a c); rewrite (Int.and_commut b c). 
  rewrite <- Int.and_or_distrib. apply Int.and_commut.
(* xor *)
  destruct args; try (exact I).
  destruct args; try (exact I).
  destruct args; try (exact I).
  generalize (H p) (H p0). simpl in *. FuncInv. subst. 
  apply approx_bitwise_correct; auto.
  intros. rewrite (Int.and_commut a c); rewrite (Int.and_commut b c). 
  rewrite <- Int.and_xor_distrib. apply Int.and_commut.
(* singleoffloat *)
  destruct args; simpl in H0; try congruence.
  destruct args; simpl in H0; try congruence.
  inv H0. destruct (rs#p); simpl; auto.
  decEq. rewrite Float.singleoffloat_idem; auto.
(* comparison *)
  simpl in H0. destruct (eval_condition c rs##args); try discriminate.
  destruct b; inv H0; compute; auto. 
Qed.

Lemma approx_of_chunk_correct:
  forall chunk m a v,
  Mem.loadv chunk m a = Some v ->
  val_match_approx (approx_of_chunk chunk) v.
Proof.
  intros. destruct a; simpl in H; try discriminate.
  exploit Mem.load_cast; eauto. 
  destruct chunk; intros; simpl; auto.
Qed.

End ANALYSIS.

(** * Correctness of the code transformation *)

Section PRESERVATION.

Variable prog: program.
Let tprog := transf_program prog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros; unfold ge, tge, tprog, transf_program. 
  apply Genv.find_symbol_transf.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros; unfold ge, tge, tprog, transf_program. 
  apply Genv.find_var_info_transf.
Qed.

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof.  
  intros.
  exact (Genv.find_funct_transf transf_fundef _ _ H).
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof.  
  intros. 
  exact (Genv.find_funct_ptr_transf transf_fundef _ _ H).
Qed.

Lemma sig_function_translated:
  forall f,
  funsig (transf_fundef f) = funsig f.
Proof.
  intros. destruct f; reflexivity.
Qed.

Lemma find_function_translated:
  forall ros rs fd,
  find_function ge ros rs = Some fd ->
  find_function tge ros rs = Some (transf_fundef fd).
Proof.
  intros. destruct ros; simpl in *. 
  apply functions_translated; auto. 
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); try congruence.
  apply function_ptr_translated; auto.
Qed.

(** Correctness of [transf_operation]. *)

Lemma transf_operation_correct:
  forall (ge: genv) app rs sp op args v,
  regs_match_approx app rs ->
  eval_operation ge sp op rs##args = Some v ->
  eval_operation ge sp (transf_operation op (approx_regs app args)) rs##args = Some v.
Proof.
  intros until v. intro RMA.
  assert (A: forall a r, Approx.bge a (approx_reg app r) = true -> val_match_approx a rs#r).
    intros. eapply val_match_approx_increasing. apply Approx.bge_correct; eauto. apply RMA.
Opaque Approx.bge.
  destruct op; simpl; auto.
(* cast8signed *)
  destruct args; simpl; try congruence. destruct args; simpl; try congruence. 
  intros EQ; inv EQ.
  caseEq (Approx.bge Int8s (approx_reg app p)); intros.
  exploit A; eauto. unfold val_match_approx. simpl. congruence.
  auto.
(* cast8unsigned *)
  destruct args; simpl; try congruence. destruct args; simpl; try congruence. 
  intros EQ; inv EQ.
  caseEq (Approx.bge Int8u (approx_reg app p)); intros.
  exploit A; eauto. unfold val_match_approx. simpl. congruence.
  auto.
(* cast8signed *)
  destruct args; simpl; try congruence. destruct args; simpl; try congruence. 
  intros EQ; inv EQ.
  caseEq (Approx.bge Int16s (approx_reg app p)); intros.
  exploit A; eauto. unfold val_match_approx. simpl. congruence.
  auto.
(* cast8unsigned *)
  destruct args; simpl; try congruence. destruct args; simpl; try congruence. 
  intros EQ; inv EQ.
  caseEq (Approx.bge Int16u (approx_reg app p)); intros.
  exploit A; eauto. unfold val_match_approx. simpl. congruence.
  auto.
(* singleoffloat *)
  destruct args; simpl; try congruence. destruct args; simpl; try congruence. 
  intros EQ; inv EQ.
  caseEq (Approx.bge Single (approx_reg app p)); intros.
  exploit A; eauto. unfold val_match_approx. simpl. congruence.
  auto.
Qed.

(** Matching between states. *)

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
   match_stackframe_intro:
      forall res sp pc rs f,
      (forall v, regs_match_approx (analyze f)!!pc (rs#res <- v)) ->
    match_stackframes
        (Stackframe res f sp pc rs)
        (Stackframe res (transf_function f) sp pc rs).

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m f s'
           (MATCH: regs_match_approx (analyze f)!!pc rs)
           (STACKS: list_forall2 match_stackframes s s'),
      match_states (State s f sp pc rs m)
                   (State s' (transf_function f) sp pc rs m)
  | match_states_call:
      forall s f args m s',
      list_forall2 match_stackframes s s' ->
      match_states (Callstate s f args m)
                   (Callstate s' (transf_fundef f) args m)
  | match_states_return:
      forall s s' v m,
      list_forall2 match_stackframes s s' ->
      match_states (Returnstate s v m)
                   (Returnstate s' v m).

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc ?c = Some ?instr), f: function |- _ =>
      cut ((transf_function f).(fn_code)!pc = Some(transf_instr (analyze f)!!pc instr));
      [ simpl transf_instr
      | unfold transf_function, transf_code; simpl; rewrite PTree.gmap; 
        unfold option_map; rewrite H1; reflexivity ]
  end.

(** The proof of semantic preservation follows from the lock-step simulation lemma below. *)

Lemma transf_step_correct:
  forall s1 t s2,
  step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; inv MS.

  (* Inop *)
  econstructor; split. 
  TransfInstr; intro. eapply exec_Inop; eauto.
  econstructor; eauto.
  eapply analyze_correct with (pc := pc); eauto.
  simpl; auto.
  unfold transfer; rewrite H. auto.

  (* Iop *)
  exists (State s' (transf_function f) sp pc' (rs#res <- v) m); split.
  TransfInstr; intro. eapply exec_Iop; eauto.
  apply transf_operation_correct; auto.
  rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto.
  eapply analyze_correct with (pc := pc); eauto.
  simpl; auto.
  unfold transfer; rewrite H. apply regs_match_approx_update; auto. 
  eapply approx_operation_correct; eauto. 

  (* Iload *)
  econstructor; split. 
  TransfInstr; intro. eapply exec_Iload with (a := a). eauto. 
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  eauto.
  econstructor; eauto.
  eapply analyze_correct with (pc := pc); eauto.
  simpl; auto.
  unfold transfer; rewrite H. apply regs_match_approx_update; auto.
  eapply approx_of_chunk_correct; eauto. 

  (* Istore *)
  econstructor; split. 
  TransfInstr; intro. eapply exec_Istore with (a := a). eauto.
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  eauto.
  econstructor; eauto.
  eapply analyze_correct with (pc := pc); eauto.
  simpl; auto.
  unfold transfer; rewrite H. auto.

  (* Icall *)
  TransfInstr; intro.
  econstructor; split.
  eapply exec_Icall. eauto. apply find_function_translated; eauto.
  apply sig_function_translated; auto.
  constructor; auto. constructor; auto.
  econstructor; eauto. 
  intros. eapply analyze_correct; eauto. simpl; auto.
  unfold transfer; rewrite H.
  apply regs_match_approx_update; auto. exact I.

  (* Itailcall *)
  TransfInstr; intro.
  econstructor; split.
  eapply exec_Itailcall. eauto. apply find_function_translated; eauto.
  apply sig_function_translated; auto.
  simpl; eauto. 
  constructor; auto.

  (* Ibuiltin *)
  TransfInstr. intro.
  exists (State s' (transf_function f) sp pc' (rs#res <- v) m'); split.
  eapply exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto. 
  eapply analyze_correct; eauto. simpl; auto. 
  unfold transfer; rewrite H. 
  apply regs_match_approx_update; auto. exact I.

  (* Icond, true *)
  exists (State s' (transf_function f) sp ifso rs m); split. 
  TransfInstr. intro.
  eapply exec_Icond_true; eauto.
  econstructor; eauto.
  eapply analyze_correct; eauto.
  simpl; auto.
  unfold transfer; rewrite H; auto.

  (* Icond, false *)
  exists (State s' (transf_function f) sp ifnot rs m); split. 
  TransfInstr. intro.
  eapply exec_Icond_false; eauto.
  econstructor; eauto.
  eapply analyze_correct; eauto.
  simpl; auto.
  unfold transfer; rewrite H; auto.

  (* Ijumptable *)
  exists (State s' (transf_function f) sp pc' rs m); split.
  TransfInstr. intro.
  eapply exec_Ijumptable; eauto.
  constructor; auto.
  eapply analyze_correct; eauto.
  simpl. eapply list_nth_z_in; eauto.
  unfold transfer; rewrite  H; auto.

  (* Ireturn *)
  exists (Returnstate s' (regmap_optget or Vundef rs) m'); split.
  eapply exec_Ireturn; eauto. TransfInstr; auto.
  constructor; auto.

  (* internal function *)
  simpl. unfold transf_function.
  econstructor; split.
  eapply exec_function_internal; simpl; eauto.
  simpl. econstructor; eauto.
  apply analyze_correct_start; auto.

  (* external function *)
  simpl. econstructor; split.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.

  (* return *)
  inv H3. inv H1. 
  econstructor; split.
  eapply exec_return; eauto. 
  econstructor; eauto. 
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intro FIND.
  exists (Callstate nil (transf_fundef f) nil m0); split.
  econstructor; eauto.
  apply Genv.init_mem_transf; auto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  reflexivity.
  rewrite <- H3. apply sig_function_translated.
  constructor. constructor.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H4. constructor. 
Qed.

(** The preservation of the observable behavior of the program then
  follows, using the generic preservation theorem
  [Smallstep.simulation_step_preservation]. *)

Theorem transf_program_correct:
  forall (beh: program_behavior), not_wrong beh ->
  exec_program prog beh -> exec_program tprog beh.
Proof.
  unfold exec_program; intros.
  eapply simulation_step_preservation; eauto.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transf_step_correct. 
Qed.

End PRESERVATION.



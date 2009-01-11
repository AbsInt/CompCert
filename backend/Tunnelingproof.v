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

(** Correctness proof for the branch tunneling optimization. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import Tunneling.

(** * Properties of branch target computation *)

Lemma is_goto_instr_correct:
  forall b s,
  is_goto_instr b = Some s -> b = Some (Lnop s).
Proof.
  unfold is_goto_instr; intros.
  destruct b; try discriminate.
  destruct i; discriminate || congruence. 
Qed. 

Lemma branch_target_rec_1:
  forall f pc n,
  branch_target_rec f pc n = Some pc
  \/ branch_target_rec f pc n = None
  \/ exists pc', f.(fn_code)!pc = Some(Lnop pc').
Proof.
  intros. destruct n; simpl.
  right; left; auto.
  caseEq (is_goto_instr f.(fn_code)!pc); intros.
  right; right. exists n0. apply is_goto_instr_correct; auto.
  left; auto.
Qed.

Lemma branch_target_rec_2:
  forall f n pc1 pc2 pc3,
  f.(fn_code)!pc1 = Some (Lnop pc2) ->
  branch_target_rec f pc1 n = Some pc3 ->
  branch_target_rec f pc2 n = Some pc3.
Proof.
  induction n. 
  simpl. intros; discriminate.
  intros pc1 pc2 pc3 ATpc1 H. simpl in H. 
  unfold is_goto_instr in H; rewrite ATpc1 in H.
  simpl. caseEq (is_goto_instr f.(fn_code)!pc2); intros.
  apply IHn with pc2. apply is_goto_instr_correct; auto. auto.
  destruct n; simpl in H. discriminate. rewrite H0 in H. auto.
Qed.

(** Counting the number of consecutive gotos. *)

Fixpoint count_goto_rec (f: LTL.function) (pc: node) (count: nat)
                        {struct count} : nat :=
  match count with
  | Datatypes.O => Datatypes.O
  | Datatypes.S count' =>
      match is_goto_instr f.(fn_code)!pc with
      | Some s => Datatypes.S (count_goto_rec f s count')
      | None => Datatypes.O
      end
    end.

Definition count_goto (f: LTL.function) (pc: node) : nat :=
  count_goto_rec f pc 10%nat.

Lemma count_goto_rec_prop:
  forall f n pc1 pc2 pc3,
  f.(fn_code)!pc1 = Some (Lnop pc2) ->
  branch_target_rec f pc1 n = Some pc3 ->
  (count_goto_rec f pc2 n < count_goto_rec f pc1 n)%nat.
Proof.
  induction n.
  simpl; intros. discriminate.
  intros pc1 pc2 pc3 ATpc1 H. simpl in H. 
  unfold is_goto_instr in H; rewrite ATpc1 in H.
  simpl. unfold is_goto_instr at 2. rewrite ATpc1. 
  caseEq (is_goto_instr f.(fn_code)!pc2); intros.
  exploit (IHn pc2); eauto. apply is_goto_instr_correct; eauto. 
  omega.
  omega.
Qed.

(** The following lemma captures the property of [branch_target]
  on which the proof of semantic preservation relies. *)

Lemma branch_target_characterization:
  forall f pc,
  branch_target f pc = pc \/
  (exists pc', f.(fn_code)!pc = Some(Lnop pc')
            /\ branch_target f pc' = branch_target f pc
            /\ count_goto f pc' < count_goto f pc)%nat.
Proof.
  intros. unfold branch_target. 
  generalize (branch_target_rec_1 f pc 10%nat). 
  intros [A|[A|[pc' AT]]].
  rewrite A. left; auto.
  rewrite A. left; auto.
  caseEq (branch_target_rec f pc 10%nat). intros pcx BT.
  right. exists pc'. split. auto. 
  split. rewrite (branch_target_rec_2 _ _ _ _ _ AT BT). auto.
  unfold count_goto. eapply count_goto_rec_prop; eauto. 
  intro. left; auto.
Qed.

(** * Preservation of semantics *)

Section PRESERVATION.

Variable p: program.
Let tp := tunnel_program p.
Let ge := Genv.globalenv p.
Let tge := Genv.globalenv tp.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (tunnel_fundef f).
Proof (@Genv.find_funct_transf _ _ _ tunnel_fundef p).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (tunnel_fundef f).
Proof (@Genv.find_funct_ptr_transf _ _ _ tunnel_fundef p).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (@Genv.find_symbol_transf _ _ _ tunnel_fundef p).

Lemma sig_preserved:
  forall f, funsig (tunnel_fundef f) = funsig f.
Proof.
  destruct f; reflexivity.
Qed.

Lemma find_function_translated:
  forall ros ls f,
  find_function ge ros ls = Some f ->
  find_function tge ros ls = Some (tunnel_fundef f).
Proof.
  intros until f. destruct ros; simpl.
  intro. apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply function_ptr_translated; auto.
  congruence.
Qed.

(** The proof of semantic preservation is a simulation argument
  based on diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                  ?|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The [match_states] predicate, defined below, captures the precondition
  between states [st1] and [st2], as well as the postcondition between
  [st1'] and [st2'].  One transition in the source code (left) can correspond
  to zero or one transition in the transformed code (right).  The
  "zero transition" case occurs when executing a [Lgoto] instruction
  in the source code that has been removed by tunneling.

  In the definition of [match_states], note that only the control-flow
  (in particular, the current program point [pc]) is changed:
  the values of locations and the memory states are identical in the
  original and transformed codes. *)

Definition tunneled_code (f: function) :=
  PTree.map (fun pc b => tunnel_instr f b) (fn_code f).

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  | match_stackframes_intro:
      forall res f sp ls0 pc,
      match_stackframes
         (Stackframe res f sp ls0 pc)
         (Stackframe res (tunnel_function f) sp ls0 (branch_target f pc)).

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s f sp pc ls m ts,
      list_forall2 match_stackframes s ts ->
      match_states (State s f sp pc ls m)
                   (State ts (tunnel_function f) sp (branch_target f pc) ls m)
  | match_states_call:
      forall s f ls m ts,
      list_forall2 match_stackframes s ts ->
      match_states (Callstate s f ls m)
                   (Callstate ts (tunnel_fundef f) ls m)
  | match_states_return:
      forall s ls m ts,
      list_forall2 match_stackframes s ts ->
      match_states (Returnstate s ls m)
                   (Returnstate ts ls m).

(** To preserve non-terminating behaviours, we show that the transformed
  code cannot take an infinity of "zero transition" cases.
  We use the following [measure] function over source states,
  which decreases strictly in the "zero transition" case. *)

Definition measure (st: state) : nat :=
  match st with
  | State s f sp pc ls m => count_goto f pc
  | Callstate s f ls m => 0%nat
  | Returnstate s ls m => 0%nat
  end.

Lemma branch_target_identity:
  forall f pc,
  match f.(fn_code)!pc with Some(Lnop _) => False | _ => True end ->
  branch_target f pc = pc.
Proof.
  intros. 
  destruct (branch_target_characterization f pc) as [A | [pc' [B C]]].
  auto. rewrite B in H. contradiction.
Qed.

Lemma tunnel_function_lookup:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  (tunnel_function f).(fn_code)!pc = Some (tunnel_instr f i).
Proof.
  intros. simpl. rewrite PTree.gmap. rewrite H. auto.
Qed.

Lemma tunnel_step_correct:
  forall st1 t st2, step ge st1 t st2 ->
  forall st1' (MS: match_states st1 st1'),
  (exists st2', step tge st1' t st2' /\ match_states st2 st2')
  \/ (measure st2 < measure st1 /\ t = E0 /\ match_states st2 st1')%nat.
Proof.
  induction 1; intros; try inv MS.
  (* Lnop *)
  destruct (branch_target_characterization f pc) as [A | [pc1 [B [C D]]]].
  left; econstructor; split.
  eapply exec_Lnop. rewrite A. 
  rewrite (tunnel_function_lookup _ _ _ H); simpl; auto.  
  econstructor; eauto. 
  assert (pc1 = pc') by congruence. subst pc1.
  right. split. simpl. auto. split. auto. 
  rewrite <- C. econstructor; eauto. 
  (* Lop *)
  rewrite (branch_target_identity f pc); [idtac | rewrite H; auto].
  left; econstructor; split.
  eapply exec_Lop with (v := v); eauto.
  rewrite (tunnel_function_lookup _ _ _ H); simpl; auto.  
  rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto.
  (* Lload *)
  rewrite (branch_target_identity f pc); [idtac | rewrite H; auto].
  left; econstructor; split.
  eapply exec_Lload; eauto.
  rewrite (tunnel_function_lookup _ _ _ H); simpl; auto.  
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  econstructor; eauto.
  (* Lstore *)
  rewrite (branch_target_identity f pc); [idtac | rewrite H; auto].
  left; econstructor; split.
  eapply exec_Lstore; eauto.
  rewrite (tunnel_function_lookup _ _ _ H); simpl; auto.  
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  econstructor; eauto.
  (* Lcall *)
  left; econstructor; split. 
  eapply exec_Lcall with (f' := tunnel_fundef f'); eauto.
  rewrite (branch_target_identity f pc); [idtac | rewrite H; auto].
  rewrite (tunnel_function_lookup _ _ _ H); simpl.
  rewrite sig_preserved. auto.
  apply find_function_translated; auto.
  econstructor; eauto.
  constructor; auto. 
  constructor; auto.
  (* Ltailcall *)
  left; econstructor; split. 
  eapply exec_Ltailcall with (f' := tunnel_fundef f'); eauto.
  rewrite (branch_target_identity f pc); [idtac | rewrite H; auto].
  rewrite (tunnel_function_lookup _ _ _ H); simpl.
  rewrite sig_preserved. auto.
  apply find_function_translated; auto.
  econstructor; eauto.
  (* cond *)
  rewrite (branch_target_identity f pc); [idtac | rewrite H; auto].
  left; econstructor; split.
  eapply exec_Lcond_true; eauto.
  rewrite (tunnel_function_lookup _ _ _ H); simpl; eauto.
  econstructor; eauto.
  rewrite (branch_target_identity f pc); [idtac | rewrite H; auto].
  left; econstructor; split.
  eapply exec_Lcond_false; eauto.
  rewrite (tunnel_function_lookup _ _ _ H); simpl; eauto.
  econstructor; eauto.
  (* return *)
  rewrite (branch_target_identity f pc); [idtac | rewrite H; auto].
  left; econstructor; split.
  eapply exec_Lreturn; eauto.
  rewrite (tunnel_function_lookup _ _ _ H); simpl; eauto.
  simpl. constructor; auto.
  (* internal function *)
  simpl. left; econstructor; split.
  eapply exec_function_internal; eauto.
  simpl. econstructor; eauto. 
  (* external function *)
  simpl. left; econstructor; split.
  eapply exec_function_external; eauto.
  simpl. econstructor; eauto. 
  (* return *)
  inv H3. inv H1.
  left; econstructor; split.
  eapply exec_return; eauto.
  constructor. auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state p st1 ->
  exists st2, initial_state tp st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. 
  exists (Callstate nil (tunnel_fundef f) nil (Genv.init_mem tp)); split.
  econstructor; eauto.
  change (prog_main tp) with (prog_main p).
  rewrite symbols_preserved. eauto.
  apply function_ptr_translated; auto.
  rewrite <- H2. apply sig_preserved. 
  replace (Genv.init_mem tp) with (Genv.init_mem p).
  constructor. constructor. auto.
  symmetry. unfold tp, tunnel_program. apply Genv.init_mem_transf.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H4. constructor.  
Qed.

Theorem transf_program_correct:
  forall (beh: program_behavior),
  exec_program p beh -> exec_program tp beh.
Proof.
  unfold exec_program; intros.
  eapply simulation_opt_preservation; eauto.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact tunnel_step_correct. 
Qed.

End PRESERVATION.

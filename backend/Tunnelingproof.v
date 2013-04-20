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
Require Import UnionFind.
Require Import AST.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import Tunneling.

(** * Properties of the branch map computed using union-find. *)

(** A variant of [record_goto] that also incrementally computes a measure [f: node -> nat]
  counting the number of [Lnop] instructions starting at a given [pc] that were eliminated. *)

Definition measure_edge (u: U.t) (pc s: node) (f: node -> nat) : node -> nat :=
  fun x => if peq (U.repr u s) pc then f x
           else if peq (U.repr u x) pc then (f x + f s + 1)%nat
           else f x.

Definition record_goto' (uf: U.t * (node -> nat)) (pc: node) (b: bblock) : U.t * (node -> nat) :=
  match b with
  | Lbranch s :: b' => let (u, f) := uf in (U.union u pc s, measure_edge u pc s f)
  | _ => uf
  end.

Definition branch_map_correct (c: code) (uf: U.t * (node -> nat)): Prop :=
  forall pc,
  match c!pc with
  | Some(Lbranch s :: b) =>
      U.repr (fst uf) pc = pc \/ (U.repr (fst uf) pc = U.repr (fst uf) s /\ snd uf s < snd uf pc)%nat
  | _ =>
      U.repr (fst uf) pc = pc
  end.

Lemma record_gotos'_correct:
  forall c,
  branch_map_correct c (PTree.fold record_goto' c (U.empty, fun (x: node) => O)).
Proof.
  intros.
  apply PTree_Properties.fold_rec with (P := fun c uf => branch_map_correct c uf).

(* extensionality *)
  intros. red; intros. rewrite <- H. apply H0.

(* base case *)
  red; intros; simpl. rewrite PTree.gempty. apply U.repr_empty.

(* inductive case *)
  intros m uf pc bb; intros. destruct uf as [u f]. 
  assert (PC: U.repr u pc = pc). 
    generalize (H1 pc). rewrite H. auto.
  assert (record_goto' (u, f) pc bb = (u, f)
          \/ exists s, exists bb', bb = Lbranch s :: bb' /\ record_goto' (u, f) pc bb = (U.union u pc s, measure_edge u pc s f)).
    unfold record_goto'; simpl. destruct bb; auto. destruct i; auto. right. exists s; exists bb; auto.
  destruct H2 as [B | [s [bb' [EQ B]]]].

(* u and f are unchanged *)
  rewrite B.
  red. intro pc'. simpl. rewrite PTree.gsspec. destruct (peq pc' pc). subst pc'. 
  destruct bb; auto. destruct i; auto.
  apply H1. 

(* b is Lbranch s, u becomes union u pc s, f becomes measure_edge u pc s f *)
  rewrite B.
  red. intro pc'. simpl. rewrite PTree.gsspec. destruct (peq pc' pc). subst pc'. rewrite EQ.

(* The new instruction *)
  rewrite (U.repr_union_2 u pc s); auto. rewrite U.repr_union_3. 
  unfold measure_edge. destruct (peq (U.repr u s) pc). auto. right. split. auto.
  rewrite PC. rewrite peq_true. omega.

(* An old instruction *)
  assert (U.repr u pc' = pc' -> U.repr (U.union u pc s) pc' = pc').
    intro. rewrite <- H2 at 2. apply U.repr_union_1. congruence. 
  generalize (H1 pc'). simpl. destruct (m!pc'); auto. destruct b; auto. destruct i; auto.
  intros [P | [P Q]]. left; auto. right.
  split. apply U.sameclass_union_2. auto.
  unfold measure_edge. destruct (peq (U.repr u s) pc). auto.
  rewrite P. destruct (peq (U.repr u s0) pc). omega. auto. 
Qed.

Definition record_gotos' (f: function) :=
  PTree.fold record_goto' f.(fn_code) (U.empty, fun (x: node) => O).

Lemma record_gotos_gotos':
  forall f, fst (record_gotos' f) = record_gotos f.
Proof.
  intros. unfold record_gotos', record_gotos. 
  repeat rewrite PTree.fold_spec.
  generalize (PTree.elements (fn_code f)) (U.empty) (fun _ : node => O).
  induction l; intros; simpl.
  auto.
  unfold record_goto' at 2. unfold record_goto at 2. 
  destruct (snd a). apply IHl. destruct i; apply IHl.
Qed.

Definition branch_target (f: function) (pc: node) : node :=
  U.repr (record_gotos f) pc.

Definition count_gotos (f: function) (pc: node) : nat :=
  snd (record_gotos' f) pc.

Theorem record_gotos_correct:
  forall f pc,
  match f.(fn_code)!pc with
  | Some(Lbranch s :: b) =>
       branch_target f pc = pc \/
       (branch_target f pc = branch_target f s /\ count_gotos f s < count_gotos f pc)%nat
  | _ => branch_target f pc = pc
  end.
Proof.
  intros. 
  generalize (record_gotos'_correct f.(fn_code) pc). simpl.
  fold (record_gotos' f). unfold branch_map_correct, branch_target, count_gotos.
  rewrite record_gotos_gotos'. auto.
Qed.

(** * Preservation of semantics *)

Section PRESERVATION.

Variable prog: program.
Let tprog := tunnel_program prog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (tunnel_fundef f).
Proof (@Genv.find_funct_transf _ _ _ tunnel_fundef prog).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (tunnel_fundef f).
Proof (@Genv.find_funct_ptr_transf _ _ _ tunnel_fundef prog).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (@Genv.find_symbol_transf _ _ _ tunnel_fundef prog).

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof (@Genv.find_var_info_transf _ _ _ tunnel_fundef prog).

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

Definition tunneled_block (f: function) (b: bblock) :=
  tunnel_block (record_gotos f) b.

Definition tunneled_code (f: function) :=
  PTree.map1 (tunneled_block f) (fn_code f).

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  | match_stackframes_intro:
      forall f sp ls0 bb,
      match_stackframes
         (Stackframe f sp ls0 bb)
         (Stackframe (tunnel_function f) sp ls0 (tunneled_block f bb)).

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s f sp pc ls m ts,
      list_forall2 match_stackframes s ts ->
      match_states (State s f sp pc ls m)
                   (State ts (tunnel_function f) sp (branch_target f pc) ls m)
  | match_states_block:
      forall s f sp bb ls m ts,
      list_forall2 match_stackframes s ts ->
      match_states (Block s f sp bb ls m)
                   (Block ts (tunnel_function f) sp (tunneled_block f bb) ls m)
  | match_states_interm:
      forall s f sp pc bb ls m ts,
      list_forall2 match_stackframes s ts ->
      match_states (Block s f sp (Lbranch pc :: bb) ls m)
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
  | State s f sp pc ls m => (count_gotos f pc * 2)%nat
  | Block s f sp (Lbranch pc :: _) ls m => (count_gotos f pc * 2 + 1)%nat
  | Block s f sp bb ls m => 0%nat
  | Callstate s f ls m => 0%nat
  | Returnstate s ls m => 0%nat
  end.

Lemma match_parent_locset:
  forall s ts,
  list_forall2 match_stackframes s ts ->
  parent_locset ts = parent_locset s.
Proof.
  induction 1; simpl. auto. inv H; auto.
Qed.

Lemma tunnel_step_correct:
  forall st1 t st2, step ge st1 t st2 ->
  forall st1' (MS: match_states st1 st1'),
  (exists st2', step tge st1' t st2' /\ match_states st2 st2')
  \/ (measure st2 < measure st1 /\ t = E0 /\ match_states st2 st1')%nat.
Proof.
  induction 1; intros; try inv MS.

  (* entering a block *)
  assert (DEFAULT: branch_target f pc = pc ->
    (exists st2' : state,
     step tge (State ts (tunnel_function f) sp (branch_target f pc) rs m) E0 st2'
     /\ match_states (Block s f sp bb rs m) st2')).
  intros. rewrite H0. econstructor; split. 
  econstructor. simpl. rewrite PTree.gmap1. rewrite H. simpl. eauto. 
  econstructor; eauto.

  generalize (record_gotos_correct f pc). rewrite H. 
  destruct bb; auto. destruct i; auto. 
  intros [A | [B C]]. auto. 
  right. split. simpl. omega. 
  split. auto.
  rewrite B. econstructor; eauto.

  (* Lop *)
  left; simpl; econstructor; split.
  eapply exec_Lop with (v := v); eauto.
  rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto.
  (* Lload *)
  left; simpl; econstructor; split.
  eapply exec_Lload with (a := a). 
  rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  eauto. eauto.
  econstructor; eauto.
  (* Lgetstack *)
  left; simpl; econstructor; split.
  econstructor; eauto.
  econstructor; eauto.
  (* Lsetstack *)
  left; simpl; econstructor; split.
  econstructor; eauto.
  econstructor; eauto.
  (* Lstore *)
  left; simpl; econstructor; split.
  eapply exec_Lstore with (a := a).
  rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  eauto. eauto.
  econstructor; eauto.
  (* Lcall *)
  left; simpl; econstructor; split. 
  eapply exec_Lcall with (fd := tunnel_fundef fd); eauto.
  apply find_function_translated; auto.
  rewrite sig_preserved. auto.
  econstructor; eauto.
  constructor; auto. 
  constructor; auto.
  (* Ltailcall *)
  left; simpl; econstructor; split. 
  eapply exec_Ltailcall with (fd := tunnel_fundef fd); eauto.
  erewrite match_parent_locset; eauto. 
  apply find_function_translated; auto.
  apply sig_preserved.
  erewrite <- match_parent_locset; eauto.
  econstructor; eauto.
  (* Lbuiltin *)
  left; simpl; econstructor; split.
  eapply exec_Lbuiltin; eauto. 
  eapply external_call_symbols_preserved'; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.
  (* Lannot *)
  left; simpl; econstructor; split.
  eapply exec_Lannot; eauto. 
  eapply external_call_symbols_preserved'; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.

  (* Lbranch (preserved) *)
  left; simpl; econstructor; split.
  eapply exec_Lbranch; eauto. 
  fold (branch_target f pc). econstructor; eauto.
  (* Lbranch (eliminated) *)
  right; split. simpl. omega. split. auto. constructor; auto. 

  (* Lcond *)
  left; simpl; econstructor; split.
  eapply exec_Lcond; eauto.
  destruct b; econstructor; eauto.
  (* Ljumptable *)
  left; simpl; econstructor; split.
  eapply exec_Ljumptable. 
  eauto. rewrite list_nth_z_map. change U.elt with node. rewrite H0. reflexivity. eauto.
  econstructor; eauto. 
  (* Lreturn *)
  left; simpl; econstructor; split.
  eapply exec_Lreturn; eauto.
  erewrite <- match_parent_locset; eauto.
  constructor; auto.
  (* internal function *)
  left; simpl; econstructor; split.
  eapply exec_function_internal; eauto.
  simpl. econstructor; eauto. 
  (* external function *)
  left; simpl; econstructor; split.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved'; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  simpl. econstructor; eauto. 
  (* return *)
  inv H3. inv H1.
  left; econstructor; split.
  eapply exec_return; eauto.
  constructor; auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. 
  exists (Callstate nil (tunnel_fundef f) (Locmap.init Vundef) m0); split.
  econstructor; eauto.
  apply Genv.init_mem_transf; auto.
  change (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  apply function_ptr_translated; auto.
  rewrite <- H3. apply sig_preserved. 
  constructor. constructor.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H6. econstructor; eauto.  
Qed.

Theorem transf_program_correct:
  forward_simulation (LTL.semantics prog) (LTL.semantics tprog).
Proof.
  eapply forward_simulation_opt.
  eexact symbols_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact tunnel_step_correct. 
Qed.

End PRESERVATION.

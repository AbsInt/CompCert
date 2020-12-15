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

Require Import FunInd.
Require Import Coqlib Maps UnionFind.
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations LTL.
Require Import Tunneling.

Definition match_prog (p tp: program) :=
  match_program (fun ctx f tf => tf = tunnel_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (tunnel_program p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.

(** * Properties of the branch map computed using union-find. *)

Section BRANCH_MAP_CORRECT.

Variable fn: LTL.function.

Definition measure_branch (u: U.t) (pc s: node) (f: node -> nat) : node -> nat :=
  fun x => if peq (U.repr u s) pc then f x
           else if peq (U.repr u x) pc then (f x + f s + 1)%nat
           else f x.

Definition measure_cond (u: U.t) (pc s1 s2: node) (f: node -> nat) : node -> nat :=
  fun x => if peq (U.repr u s1) pc then f x
           else if peq (U.repr u x) pc then (f x + Nat.max (f s1) (f s2) + 1)%nat
           else f x.

Definition branch_map_correct_1 (c: code) (u: U.t) (f: node -> nat): Prop :=
  forall pc,
  match c!pc with
  | Some(Lbranch s :: b) =>
      U.repr u pc = pc \/ (U.repr u pc = U.repr u s /\ f s < f pc)%nat
  | _ =>
      U.repr u pc = pc
  end.

Lemma record_branch_correct:
  forall c u f pc b,
  branch_map_correct_1 (PTree.remove pc c) u f ->
  c!pc = Some b ->
  { f' | branch_map_correct_1 c (record_branch u pc b) f' }.
Proof.
  intros c u f pc b BMC GET1.
  assert (PC: U.repr u pc = pc).
  { specialize (BMC pc). rewrite PTree.grs in BMC. auto. }
  assert (DFL: { f | branch_map_correct_1 c u f }).
  { exists f. intros p. destruct (peq p pc).
  - subst p. rewrite GET1. destruct b as [ | [] b ]; auto.
  - specialize (BMC p). rewrite PTree.gro in BMC by auto. exact BMC.
  }
  unfold record_branch. destruct b as [ | [] b ]; auto.
  exists (measure_branch u pc s f). intros p. destruct (peq p pc).
+ subst p. rewrite GET1. unfold measure_branch.
  rewrite (U.repr_union_2 u pc s); auto. rewrite U.repr_union_3.
  destruct (peq (U.repr u s) pc); auto. rewrite PC, peq_true. right; split; auto. lia.
+ specialize (BMC p). rewrite PTree.gro in BMC by auto.
  assert (U.repr u p = p -> U.repr (U.union u pc s) p = p).
  { intro. rewrite <- H at 2. apply U.repr_union_1. congruence. }
  destruct (c!p) as [ [ | [] _ ] | ]; auto.
  destruct BMC as [A | [A B]]. auto.
  right; split. apply U.sameclass_union_2; auto.
  unfold measure_branch. destruct (peq (U.repr u s) pc). auto.
  rewrite A. destruct (peq (U.repr u s0) pc); lia.
Qed.

Lemma record_branches_correct:
  { f | branch_map_correct_1 fn.(fn_code) (record_branches fn) f }.
Proof.
  unfold record_branches. apply PTree_Properties.fold_ind.
- (* base case *)
  intros m EMPTY. exists (fun _ => O). 
  red; intros. rewrite EMPTY. apply U.repr_empty.
- (* inductive case *)
  intros m u pc bb GET1 GET2 [f BMC]. eapply record_branch_correct; eauto.
Qed.

Definition branch_map_correct_2 (c: code) (u: U.t) (f: node -> nat): Prop :=
  forall pc,
  match fn.(fn_code)!pc with
  | Some(Lbranch s :: b) =>
      U.repr u pc = pc \/ (U.repr u pc = U.repr u s /\ f s < f pc)%nat
  | Some(Lcond cond args s1 s2 :: b) =>
      U.repr u pc = pc \/ (c!pc = None /\ U.repr u pc = U.repr u s1 /\ U.repr u pc = U.repr u s2 /\ f s1 < f pc /\ f s2 < f pc)%nat
  | _ =>
      U.repr u pc = pc
  end.

Lemma record_cond_correct:
  forall c u changed f pc b,
  branch_map_correct_2 c u f ->
  fn.(fn_code)!pc = Some b ->
  c!pc <> None ->
  let '(c1, u1, _) := record_cond (c, u, changed) pc b in
  { f' | branch_map_correct_2 c1 u1 f' }.
Proof.
  intros c u changed f pc b BMC GET1 GET2.
  assert (DFL: { f' | branch_map_correct_2 c u f' }).
  { exists f; auto. }
  unfold record_cond. destruct b as [ | [] b ]; auto.
  destruct (peq (U.repr u s1) (U.repr u s2)); auto.
  exists (measure_cond u pc s1 s2 f).
  assert (PC: U.repr u pc = pc).
  { specialize (BMC pc). rewrite GET1 in BMC. intuition congruence. }
  intro p. destruct (peq p pc).
- subst p. rewrite GET1. unfold measure_cond.
  rewrite U.repr_union_2 by auto. rewrite <- e, PC, peq_true.
  destruct (peq (U.repr u s1) pc); auto.
  right; repeat split.
  + apply PTree.grs.
  + rewrite U.repr_union_3. auto.
  + rewrite U.repr_union_1 by congruence. auto.
  + lia.
  + lia.
- assert (P: U.repr u p = p -> U.repr (U.union u pc s1) p = p).
  { intros. rewrite U.repr_union_1 by congruence. auto. }
  specialize (BMC p). destruct (fn_code fn)!p as [ [ | [] bb ] | ]; auto.
  + destruct BMC as [A | (A & B)]; auto. right; split.
    * apply U.sameclass_union_2; auto.
    * unfold measure_cond. rewrite <- A.
      destruct (peq (U.repr u s1) pc). auto.
      destruct (peq (U.repr u p) pc); lia.
  + destruct BMC as [A | (A & B & C & D & E)]; auto. right; split; [ | split; [ | split]].
    * rewrite PTree.gro by auto. auto.
    * apply U.sameclass_union_2; auto.
    * apply U.sameclass_union_2; auto.
    * unfold measure_cond. rewrite <- B, <- C.
      destruct (peq (U.repr u s1) pc). auto.
      destruct (peq (U.repr u p) pc); lia.
Qed.

Definition code_compat (c: code) : Prop :=
  forall pc b, c!pc = Some b -> fn.(fn_code)!pc = Some b.

Definition code_invariant (c0 c1 c2: code) : Prop :=
  forall pc, c0!pc = None -> c1!pc = c2!pc.

Lemma record_conds_1_correct:
  forall c u f,
  branch_map_correct_2 c u f ->
  code_compat c ->
  let '(c', u', _) := record_conds_1 (c, u) in
  (code_compat c' * { f' | branch_map_correct_2 c' u' f' })%type.
Proof.
  intros c0 u0 f0 BMC0 COMPAT0.
  unfold record_conds_1.
  set (x := PTree.fold record_cond c0 (c0, u0, false)).
  set (P := fun (cd: code) (cuc: code * U.t * bool) =>
            (code_compat (fst (fst cuc)) *
             code_invariant cd (fst (fst cuc)) c0 *
             { f | branch_map_correct_2 (fst (fst cuc)) (snd (fst cuc)) f })%type).
  assert (REC: P c0 x).
  { unfold x; apply PTree_Properties.fold_ind.
  - intros cd EMPTY. split; [split|]; simpl.
    + auto.
    + red; auto.
    + exists f0; auto.
  - intros cd [[c u] changed] pc b GET1 GET2 [[COMPAT INV] [f BMC]]. simpl in *.
    split; [split|].
    + unfold record_cond; destruct b as [ | [] b]; simpl; auto.
      destruct (peq (U.repr u s1) (U.repr u s2)); simpl; auto.
      red; intros. rewrite PTree.grspec in H. destruct (PTree.elt_eq pc0 pc). discriminate. auto.
    + assert (DFL: code_invariant cd c c0).
      { intros p GET. apply INV. rewrite PTree.gro by congruence. auto. }
      unfold record_cond; destruct b as [ | [] b]; simpl; auto.
      destruct (peq (U.repr u s1) (U.repr u s2)); simpl; auto.
      intros p GET. rewrite PTree.gro by congruence. apply INV. rewrite PTree.gro by congruence. auto.
    + assert (GET3: c!pc = Some b).
      { rewrite <- GET2. apply INV. apply PTree.grs. }
      assert (X: fn.(fn_code)!pc = Some b) by auto.
      assert (Y: c!pc <> None) by congruence.
      generalize (record_cond_correct c u changed f pc b BMC X Y).
      destruct (record_cond (c, u, changed) pc b) as [[c1 u1] changed1]; simpl.
      auto.
  }
  destruct x as [[c1 u1] changed1]; destruct REC as [[COMPAT1 INV1] BMC1]; auto.
Qed.

Definition branch_map_correct (u: U.t) (f: node -> nat): Prop :=
  forall pc,
  match fn.(fn_code)!pc with
  | Some(Lbranch s :: b) =>
      U.repr u pc = pc \/ (U.repr u pc = U.repr u s /\ f s < f pc)%nat
  | Some(Lcond cond args s1 s2 :: b) =>
      U.repr u pc = pc \/ (U.repr u pc = U.repr u s1 /\ U.repr u pc = U.repr u s2 /\ f s1 < f pc /\ f s2 < f pc)%nat
  | _ =>
      U.repr u pc = pc
  end.

Lemma record_conds_correct:
  forall cu,
  { f | branch_map_correct_2 (fst cu) (snd cu) f } ->
  code_compat (fst cu) ->
  { f | branch_map_correct (record_conds cu) f }.
Proof.
  intros cu0. functional induction (record_conds cu0); intros.
- destruct cu as [c u], cu' as [c' u'], H as [f BMC]. 
  generalize (record_conds_1_correct c u f BMC H0).
  rewrite e. intros [U V]. apply IHt; auto.
- destruct cu as [c u], H as [f BMC].
  exists f. intros pc. specialize (BMC pc); simpl in *.
  destruct (fn_code fn)!pc as [ [ | [] b ] | ]; tauto.
Qed.

Lemma record_gotos_correct_1:
  { f | branch_map_correct (record_gotos fn) f }.
Proof.
  apply record_conds_correct; simpl.
- destruct record_branches_correct as [f BMC].
  exists f. intros pc. specialize (BMC pc); simpl in *.
  destruct (fn_code fn)!pc as [ [ | [] b ] | ]; auto.
- red; auto.
Qed.

Definition branch_target  (pc: node) : node :=
  U.repr (record_gotos fn) pc.

Definition count_gotos (pc: node) : nat :=
  proj1_sig record_gotos_correct_1 pc.

Theorem record_gotos_correct:
  forall pc,
  match fn.(fn_code)!pc with
  | Some(Lbranch s :: b) =>
      branch_target pc = pc \/
      (branch_target pc = branch_target s /\ count_gotos s < count_gotos pc)%nat
  | Some(Lcond cond args s1 s2 :: b) =>
      branch_target pc = pc \/
      (branch_target pc = branch_target s1 /\ branch_target pc = branch_target s2
       /\ count_gotos s1 < count_gotos pc /\ count_gotos s2 < count_gotos pc)%nat
  | _ =>
      branch_target pc = pc
  end.
Proof.
  intros. unfold count_gotos. destruct record_gotos_correct_1 as [f P]; simpl.
  apply P.
Qed.

End BRANCH_MAP_CORRECT.

(** * Preservation of semantics *)

Section PRESERVATION.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (tunnel_fundef f).
Proof (Genv.find_funct_transf TRANSL).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (tunnel_fundef f).
Proof (Genv.find_funct_ptr_transf TRANSL).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (Genv.find_symbol_transf TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf TRANSL).

Lemma sig_preserved:
  forall f, funsig (tunnel_fundef f) = funsig f.
Proof.
  destruct f; reflexivity.
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

  In the definition of [match_states], what changes between the original and
  transformed codes is mainly the control-flow
  (in particular, the current program point [pc]), but also some values
  and memory states, since some [Vundef] values can become more defined
  as a consequence of eliminating useless [Lcond] instructions. *)

Definition tunneled_block (f: function) (b: bblock) :=
  tunnel_block (record_gotos f) b.

Definition tunneled_code (f: function) :=
  PTree.map1 (tunneled_block f) (fn_code f).

Definition locmap_lessdef (ls1 ls2: locset) : Prop :=
  forall l, Val.lessdef (ls1 l) (ls2 l).

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  | match_stackframes_intro:
      forall f sp ls0 bb tls0,
      locmap_lessdef ls0 tls0 ->
      match_stackframes
         (Stackframe f sp ls0 bb)
         (Stackframe (tunnel_function f) sp tls0 (tunneled_block f bb)).

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s f sp pc ls m ts tls tm
        (STK: list_forall2 match_stackframes s ts)
        (LS: locmap_lessdef ls tls)
        (MEM: Mem.extends m tm),
      match_states (State s f sp pc ls m)
                   (State ts (tunnel_function f) sp (branch_target f pc) tls tm)
  | match_states_block:
      forall s f sp bb ls m ts tls tm
        (STK: list_forall2 match_stackframes s ts)
        (LS: locmap_lessdef ls tls)
        (MEM: Mem.extends m tm),
      match_states (Block s f sp bb ls m)
                   (Block ts (tunnel_function f) sp (tunneled_block f bb) tls tm)
  | match_states_interm_branch:
      forall s f sp pc bb ls m ts tls tm
        (STK: list_forall2 match_stackframes s ts)
        (LS: locmap_lessdef ls tls)
        (MEM: Mem.extends m tm),
      match_states (Block s f sp (Lbranch pc :: bb) ls m)
                   (State ts (tunnel_function f) sp (branch_target f pc) tls tm)
  | match_states_interm_cond:
      forall s f sp cond args pc1 pc2 bb ls m ts tls tm
        (STK: list_forall2 match_stackframes s ts)
        (LS: locmap_lessdef ls tls)
        (MEM: Mem.extends m tm)
        (SAME: branch_target f pc1 = branch_target f pc2),
      match_states (Block s f sp (Lcond cond args pc1 pc2 :: bb) ls m)
                   (State ts (tunnel_function f) sp (branch_target f pc1) tls tm)
  | match_states_call:
      forall s f ls m ts tls tm
        (STK: list_forall2 match_stackframes s ts)
        (LS: locmap_lessdef ls tls)
        (MEM: Mem.extends m tm),
      match_states (Callstate s f ls m)
                   (Callstate ts (tunnel_fundef f) tls tm)
  | match_states_return:
      forall s ls m ts tls tm
        (STK: list_forall2 match_stackframes s ts)
        (LS: locmap_lessdef ls tls)
        (MEM: Mem.extends m tm),
      match_states (Returnstate s ls m)
                   (Returnstate ts tls tm).

(** Properties of [locmap_lessdef] *)

Lemma reglist_lessdef:
  forall rl ls1 ls2,
  locmap_lessdef ls1 ls2 -> Val.lessdef_list (reglist ls1 rl) (reglist ls2 rl).
Proof.
  induction rl; simpl; intros; auto.
Qed.

Lemma locmap_set_lessdef:
  forall ls1 ls2 v1 v2 l,
  locmap_lessdef ls1 ls2 -> Val.lessdef v1 v2 -> locmap_lessdef (Locmap.set l v1 ls1) (Locmap.set l v2 ls2).
Proof.
  intros; red; intros l'. unfold Locmap.set. destruct (Loc.eq l l').
- destruct l; auto using Val.load_result_lessdef.
- destruct (Loc.diff_dec l l'); auto.
Qed.

Lemma locmap_set_undef_lessdef:
  forall ls1 ls2 l,
  locmap_lessdef ls1 ls2 -> locmap_lessdef (Locmap.set l Vundef ls1) ls2.
Proof.
  intros; red; intros l'. unfold Locmap.set. destruct (Loc.eq l l').
- destruct l; auto. destruct ty; auto. 
- destruct (Loc.diff_dec l l'); auto.
Qed.

Lemma locmap_undef_regs_lessdef:
  forall rl ls1 ls2,
  locmap_lessdef ls1 ls2 -> locmap_lessdef (undef_regs rl ls1) (undef_regs rl ls2).
Proof.
  induction rl as [ | r rl]; intros; simpl. auto. apply locmap_set_lessdef; auto. 
Qed.

Lemma locmap_undef_regs_lessdef_1:
  forall rl ls1 ls2,
  locmap_lessdef ls1 ls2 -> locmap_lessdef (undef_regs rl ls1) ls2.
Proof.
  induction rl as [ | r rl]; intros; simpl. auto. apply locmap_set_undef_lessdef; auto. 
Qed.

(*
Lemma locmap_undef_lessdef:
  forall ll ls1 ls2,
  locmap_lessdef ls1 ls2 -> locmap_lessdef (Locmap.undef ll ls1) (Locmap.undef ll ls2).
Proof.
  induction ll as [ | l ll]; intros; simpl. auto. apply IHll. apply locmap_set_lessdef; auto. 
Qed.

Lemma locmap_undef_lessdef_1:
  forall ll ls1 ls2,
  locmap_lessdef ls1 ls2 -> locmap_lessdef (Locmap.undef ll ls1) ls2.
Proof.
  induction ll as [ | l ll]; intros; simpl. auto. apply IHll. apply locmap_set_undef_lessdef; auto. 
Qed.
*)

Lemma locmap_getpair_lessdef:
  forall p ls1 ls2,
  locmap_lessdef ls1 ls2 -> Val.lessdef (Locmap.getpair p ls1) (Locmap.getpair p ls2).
Proof.
  intros; destruct p; simpl; auto using Val.longofwords_lessdef.
Qed.

Lemma locmap_getpairs_lessdef:
  forall pl ls1 ls2,
  locmap_lessdef ls1 ls2 ->
  Val.lessdef_list (map (fun p => Locmap.getpair p ls1) pl) (map (fun p => Locmap.getpair p ls2) pl).
Proof.
  intros. induction pl; simpl; auto using locmap_getpair_lessdef.
Qed.

Lemma locmap_setpair_lessdef:
  forall p ls1 ls2 v1 v2,
  locmap_lessdef ls1 ls2 -> Val.lessdef v1 v2 -> locmap_lessdef (Locmap.setpair p v1 ls1) (Locmap.setpair p v2 ls2).
Proof.
  intros; destruct p; simpl; auto using locmap_set_lessdef, Val.loword_lessdef, Val.hiword_lessdef.
Qed.

Lemma locmap_setres_lessdef:
  forall res ls1 ls2 v1 v2,
  locmap_lessdef ls1 ls2 -> Val.lessdef v1 v2 -> locmap_lessdef (Locmap.setres res v1 ls1) (Locmap.setres res v2 ls2).
Proof.
  induction res; intros; simpl; auto using locmap_set_lessdef, Val.loword_lessdef, Val.hiword_lessdef.
Qed.

Lemma locmap_undef_caller_save_regs_lessdef:
  forall ls1 ls2,
  locmap_lessdef ls1 ls2 -> locmap_lessdef (undef_caller_save_regs ls1) (undef_caller_save_regs ls2).
Proof.
  intros; red; intros. unfold undef_caller_save_regs. 
  destruct l.
- destruct (Conventions1.is_callee_save r); auto.
- destruct sl; auto.
Qed.

Lemma find_function_translated:
  forall ros ls tls fd,
  locmap_lessdef ls tls ->
  find_function ge ros ls = Some fd ->
  find_function tge ros tls = Some (tunnel_fundef fd).
Proof.
  intros. destruct ros; simpl in *.
- assert (E: tls (R m) = ls (R m)).
  { exploit Genv.find_funct_inv; eauto. intros (b & EQ). 
    generalize (H (R m)). rewrite EQ. intros LD; inv LD. auto. }
  rewrite E. apply functions_translated; auto.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge i); inv H0. 
  apply function_ptr_translated; auto.
Qed.

Lemma call_regs_lessdef:
  forall ls1 ls2, locmap_lessdef ls1 ls2 -> locmap_lessdef (call_regs ls1) (call_regs ls2).
Proof.
  intros; red; intros. destruct l as [r | [] ofs ty]; simpl; auto.
Qed.

Lemma return_regs_lessdef:
  forall caller1 callee1 caller2 callee2,
  locmap_lessdef caller1 caller2 ->
  locmap_lessdef callee1 callee2 ->
  locmap_lessdef (return_regs caller1 callee1) (return_regs caller2 callee2).
Proof.
  intros; red; intros. destruct l; simpl.
- destruct (Conventions1.is_callee_save r); auto.
- destruct sl; auto.
Qed. 

(** To preserve non-terminating behaviours, we show that the transformed
  code cannot take an infinity of "zero transition" cases.
  We use the following [measure] function over source states,
  which decreases strictly in the "zero transition" case. *)

Definition measure (st: state) : nat :=
  match st with
  | State s f sp pc ls m => (count_gotos f pc * 2)%nat
  | Block s f sp (Lbranch pc :: _) ls m => (count_gotos f pc * 2 + 1)%nat
  | Block s f sp (Lcond _ _ pc1 pc2 :: _) ls m => (Nat.max (count_gotos f pc1) (count_gotos f pc2) * 2 + 1)%nat
  | Block s f sp bb ls m => 0%nat
  | Callstate s f ls m => 0%nat
  | Returnstate s ls m => 0%nat
  end.

Lemma match_parent_locset:
  forall s ts,
  list_forall2 match_stackframes s ts ->
  locmap_lessdef (parent_locset s) (parent_locset ts).
Proof.
  induction 1; simpl.
- red; auto.
- inv H; auto.
Qed.

Lemma tunnel_step_correct:
  forall st1 t st2, step ge st1 t st2 ->
  forall st1' (MS: match_states st1 st1'),
  (exists st2', step tge st1' t st2' /\ match_states st2 st2')
  \/ (measure st2 < measure st1 /\ t = E0 /\ match_states st2 st1')%nat.
Proof.
  induction 1; intros; try inv MS.

- (* entering a block *)
  assert (DEFAULT: branch_target f pc = pc ->
    (exists st2' : state,
     step tge (State ts (tunnel_function f) sp (branch_target f pc) tls tm) E0 st2'
     /\ match_states (Block s f sp bb rs m) st2')).
  { intros. rewrite H0. econstructor; split.
    econstructor. simpl. rewrite PTree.gmap1. rewrite H. simpl. eauto.
    econstructor; eauto. }

  generalize (record_gotos_correct f pc). rewrite H.
  destruct bb; auto. destruct i; auto.
+ (* Lbranch *)
  intros [A | [B C]]. auto.
  right. split. simpl. lia.
  split. auto.
  rewrite B. econstructor; eauto.
+ (* Lcond *)
  intros [A | (B & C & D & E)]. auto.
  right. split. simpl. lia.
  split. auto.
  rewrite B. econstructor; eauto. congruence.

- (* Lop *)
  exploit eval_operation_lessdef. apply reglist_lessdef; eauto. eauto. eauto. 
  intros (tv & EV & LD).
  left; simpl; econstructor; split.
  eapply exec_Lop with (v := tv); eauto.
  rewrite <- EV. apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto using locmap_set_lessdef, locmap_undef_regs_lessdef.
- (* Lload *)
  exploit eval_addressing_lessdef. apply reglist_lessdef; eauto. eauto. 
  intros (ta & EV & LD).
  exploit Mem.loadv_extends. eauto. eauto. eexact LD. 
  intros (tv & LOAD & LD').
  left; simpl; econstructor; split.
  eapply exec_Lload with (a := ta).
  rewrite <- EV. apply eval_addressing_preserved. exact symbols_preserved.
  eauto. eauto.
  econstructor; eauto using locmap_set_lessdef, locmap_undef_regs_lessdef.
- (* Lgetstack *)
  left; simpl; econstructor; split.
  econstructor; eauto.
  econstructor; eauto using locmap_set_lessdef, locmap_undef_regs_lessdef.
- (* Lsetstack *)
  left; simpl; econstructor; split.
  econstructor; eauto.
  econstructor; eauto using locmap_set_lessdef, locmap_undef_regs_lessdef.
- (* Lstore *)
  exploit eval_addressing_lessdef. apply reglist_lessdef; eauto. eauto. 
  intros (ta & EV & LD).
  exploit Mem.storev_extends. eauto. eauto. eexact LD. apply LS.  
  intros (tm' & STORE & MEM').
  left; simpl; econstructor; split.
  eapply exec_Lstore with (a := ta).
  rewrite <- EV. apply eval_addressing_preserved. exact symbols_preserved.
  eauto. eauto.
  econstructor; eauto using locmap_undef_regs_lessdef.
- (* Lcall *)
  left; simpl; econstructor; split.
  eapply exec_Lcall with (fd := tunnel_fundef fd); eauto.
  eapply find_function_translated; eauto.
  rewrite sig_preserved. auto.
  econstructor; eauto.
  constructor; auto.
  constructor; auto.
- (* Ltailcall *)
  exploit Mem.free_parallel_extends. eauto. eauto. intros (tm' & FREE & MEM'). 
  left; simpl; econstructor; split.
  eapply exec_Ltailcall with (fd := tunnel_fundef fd); eauto.
  eapply find_function_translated; eauto using return_regs_lessdef, match_parent_locset.
  apply sig_preserved.
  econstructor; eauto using return_regs_lessdef, match_parent_locset.
- (* Lbuiltin *)
  exploit eval_builtin_args_lessdef. eexact LS. eauto. eauto. intros (tvargs & EVA & LDA).
  exploit external_call_mem_extends; eauto. intros (tvres & tm' & A & B & C & D).
  left; simpl; econstructor; split.
  eapply exec_Lbuiltin; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved. 
  eapply external_call_symbols_preserved. apply senv_preserved. eauto.
  econstructor; eauto using locmap_setres_lessdef, locmap_undef_regs_lessdef.
- (* Lbranch (preserved) *)
  left; simpl; econstructor; split.
  eapply exec_Lbranch; eauto.
  fold (branch_target f pc). econstructor; eauto.
- (* Lbranch (eliminated) *)
  right; split. simpl. lia. split. auto. constructor; auto.

- (* Lcond (preserved) *)
  simpl tunneled_block.
  set (s1 := U.repr (record_gotos f) pc1). set (s2 := U.repr (record_gotos f) pc2).
  destruct (peq s1 s2).
+ left; econstructor; split.
  eapply exec_Lbranch.
  set (pc := if b then pc1 else pc2).
  replace s1 with (branch_target f pc) by (unfold pc; destruct b; auto).
  constructor; eauto using locmap_undef_regs_lessdef_1.
+ left; econstructor; split.
  eapply exec_Lcond; eauto. eapply eval_condition_lessdef; eauto using reglist_lessdef.
  destruct b; econstructor; eauto using locmap_undef_regs_lessdef.
- (* Lcond (eliminated) *)
  right; split. simpl. destruct b; lia.
  split. auto.
  set (pc := if b then pc1 else pc2).
  replace (branch_target f pc1) with (branch_target f pc) by (unfold pc; destruct b; auto).
  econstructor; eauto.

- (* Ljumptable *)
  assert (tls (R arg) = Vint n).
  { generalize (LS (R arg)); rewrite H; intros LD; inv LD; auto. }
  left; simpl; econstructor; split.
  eapply exec_Ljumptable.
  eauto. rewrite list_nth_z_map. change U.elt with node. rewrite H0. reflexivity. eauto.
  econstructor; eauto using locmap_undef_regs_lessdef.
- (* Lreturn *)
  exploit Mem.free_parallel_extends. eauto. eauto. intros (tm' & FREE & MEM'). 
  left; simpl; econstructor; split.
  eapply exec_Lreturn; eauto.
  constructor; eauto using return_regs_lessdef, match_parent_locset.
- (* internal function *)
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros (tm' & ALLOC & MEM'). 
  left; simpl; econstructor; split.
  eapply exec_function_internal; eauto.
  simpl. econstructor; eauto using locmap_undef_regs_lessdef, call_regs_lessdef.
- (* external function *)
  exploit external_call_mem_extends; eauto using locmap_getpairs_lessdef.
  intros (tvres & tm' & A & B & C & D).
  left; simpl; econstructor; split.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  simpl. econstructor; eauto using locmap_setpair_lessdef, locmap_undef_caller_save_regs_lessdef.
- (* return *)
  inv STK. inv H1.
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
  apply (Genv.init_mem_transf TRANSL); auto.
  rewrite (match_program_main TRANSL).
  rewrite symbols_preserved. eauto.
  apply function_ptr_translated; auto.
  rewrite <- H3. apply sig_preserved.
  constructor. constructor. red; simpl; auto. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STK.
  set (p := map_rpair R (Conventions1.loc_result signature_main)) in *.
  generalize (locmap_getpair_lessdef p _ _ LS). rewrite H1; intros LD; inv LD.
  econstructor; eauto.
Qed.

Theorem transf_program_correct:
  forward_simulation (LTL.semantics prog) (LTL.semantics tprog).
Proof.
  eapply forward_simulation_opt.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact tunnel_step_correct.
Qed.

End PRESERVATION.

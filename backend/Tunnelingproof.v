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

- (* extensionality *)
  intros. red; intros. rewrite <- H. apply H0.

- (* base case *)
  red; intros; simpl. rewrite PTree.gempty. apply U.repr_empty.

- (* inductive case *)
  intros m uf pc bb; intros. destruct uf as [u f].
  assert (PC: U.repr u pc = pc).
    generalize (H1 pc). rewrite H. auto.
  assert (record_goto' (u, f) pc bb = (u, f)
          \/ exists s, exists bb', bb = Lbranch s :: bb' /\ record_goto' (u, f) pc bb = (U.union u pc s, measure_edge u pc s f)).
    unfold record_goto'; simpl. destruct bb; auto. destruct i; auto. right. exists s; exists bb; auto.
  destruct H2 as [B | [s [bb' [EQ B]]]].

+ (* u and f are unchanged *)
  rewrite B.
  red. intro pc'. simpl. rewrite PTree.gsspec. destruct (peq pc' pc). subst pc'.
  destruct bb; auto. destruct i; auto.
  apply H1.

+ (* b is Lbranch s, u becomes union u pc s, f becomes measure_edge u pc s f *)
  rewrite B.
  red. intro pc'. simpl. rewrite PTree.gsspec. destruct (peq pc' pc). subst pc'. rewrite EQ.

* (* The new instruction *)
  rewrite (U.repr_union_2 u pc s); auto. rewrite U.repr_union_3.
  unfold measure_edge. destruct (peq (U.repr u s) pc). auto. right. split. auto.
  rewrite PC. rewrite peq_true. omega.

* (* An old instruction *)
  assert (U.repr u pc' = pc' -> U.repr (U.union u pc s) pc' = pc').
  { intro. rewrite <- H2 at 2. apply U.repr_union_1. congruence. }
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
  | match_states_interm:
      forall s f sp pc bb ls m ts tls tm
        (STK: list_forall2 match_stackframes s ts)
        (LS: locmap_lessdef ls tls)
        (MEM: Mem.extends m tm),
      match_states (Block s f sp (Lbranch pc :: bb) ls m)
                   (State ts (tunnel_function f) sp (branch_target f pc) tls tm)
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
  intros [A | [B C]]. auto.
  right. split. simpl. omega.
  split. auto.
  rewrite B. econstructor; eauto.

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
  right; split. simpl. omega. split. auto. constructor; auto.

- (* Lcond *)
  simpl tunneled_block.
  set (s1 := U.repr (record_gotos f) pc1). set (s2 := U.repr (record_gotos f) pc2).
  destruct (peq s1 s2).
+ left; econstructor; split.
  eapply exec_Lbranch. 
  destruct b.
* constructor; eauto using locmap_undef_regs_lessdef_1.
* rewrite e. constructor; eauto using locmap_undef_regs_lessdef_1.
+ left; econstructor; split.
  eapply exec_Lcond; eauto. eapply eval_condition_lessdef; eauto using reglist_lessdef.
  destruct b; econstructor; eauto using locmap_undef_regs_lessdef.

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

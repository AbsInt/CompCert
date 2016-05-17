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

(** Correctness proof for code linearization *)

Require Import FSets.
Require Import Coqlib Maps Ordered Errors Lattice Kildall Integers.
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations LTL Linear.
Require Import Linearize.

Module NodesetFacts := FSetFacts.Facts(Nodeset).

Definition match_prog (p: LTL.program) (tp: Linear.program) :=
  match_program (fun ctx f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Section LINEARIZATION.

Variable prog: LTL.program.
Variable tprog: Linear.program.

Hypothesis TRANSF: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial TRANSF).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  exists tf,
  Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSF).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (Genv.find_symbol_transf_partial TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf_partial TRANSF).

Lemma sig_preserved:
  forall f tf,
  transf_fundef f = OK tf ->
  Linear.funsig tf = LTL.funsig f.
Proof.
  unfold transf_fundef, transf_partial_fundef; intros.
  destruct f. monadInv H. monadInv EQ. reflexivity.
  inv H. reflexivity.
Qed.

Lemma stacksize_preserved:
  forall f tf,
  transf_function f = OK tf ->
  Linear.fn_stacksize tf = LTL.fn_stacksize f.
Proof.
  intros. monadInv H. auto.
Qed.

Lemma find_function_translated:
  forall ros ls f,
  LTL.find_function ge ros ls = Some f ->
  exists tf,
  find_function tge ros ls = Some tf /\ transf_fundef f = OK tf.
Proof.
  unfold LTL.find_function; intros; destruct ros; simpl.
  apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply function_ptr_translated; auto.
  congruence.
Qed.

(** * Correctness of reachability analysis *)

(** The entry point of the function is reachable. *)

Lemma reachable_entrypoint:
  forall f, (reachable f)!!(f.(fn_entrypoint)) = true.
Proof.
  intros. unfold reachable.
  caseEq (reachable_aux f).
  unfold reachable_aux; intros reach A.
  assert (LBoolean.ge reach!!(f.(fn_entrypoint)) true).
  eapply DS.fixpoint_entry. eexact A. auto.
  unfold LBoolean.ge in H. tauto.
  intros. apply PMap.gi.
Qed.

(** The successors of a reachable instruction are reachable. *)

Lemma reachable_successors:
  forall f pc pc' b,
  f.(LTL.fn_code)!pc = Some b -> In pc' (successors_block b) ->
  (reachable f)!!pc = true ->
  (reachable f)!!pc' = true.
Proof.
  intro f. unfold reachable.
  caseEq (reachable_aux f).
  unfold reachable_aux. intro reach; intros.
  assert (LBoolean.ge reach!!pc' reach!!pc).
  change (reach!!pc) with ((fun pc r => r) pc (reach!!pc)).
  eapply DS.fixpoint_solution; eauto. intros; apply DS.L.eq_refl.
  elim H3; intro. congruence. auto.
  intros. apply PMap.gi.
Qed.

(** * Properties of node enumeration *)

(** An enumeration of CFG nodes is correct if the following conditions hold:
- All nodes for reachable basic blocks must be in the list.
- The list is without repetition (so that no code duplication occurs).

We prove that the result of the [enumerate] function satisfies both
conditions. *)

Lemma nodeset_of_list_correct:
  forall l s s',
  nodeset_of_list l s = OK s' ->
  list_norepet l
  /\ (forall pc, Nodeset.In pc s' <-> Nodeset.In pc s \/ In pc l)
  /\ (forall pc, In pc l -> ~Nodeset.In pc s).
Proof.
  induction l; simpl; intros.
  inv H. split. constructor. split. intro; tauto. intros; tauto.
  generalize H; clear H; caseEq (Nodeset.mem a s); intros.
  inv H0.
  exploit IHl; eauto. intros [A [B C]].
  split. constructor; auto. red; intro. elim (C a H1). apply Nodeset.add_1. hnf. auto.
  split. intros. rewrite B. rewrite NodesetFacts.add_iff.
  unfold Nodeset.E.eq. unfold OrderedPositive.eq. tauto.
  intros. destruct H1. subst pc. rewrite NodesetFacts.not_mem_iff. auto.
  generalize (C pc H1). rewrite NodesetFacts.add_iff. tauto.
Qed.

Lemma check_reachable_correct:
  forall f reach s pc i,
  check_reachable f reach s = true ->
  f.(LTL.fn_code)!pc = Some i ->
  reach!!pc = true ->
  Nodeset.In pc s.
Proof.
  intros f reach s.
  assert (forall l ok,
    List.fold_left (fun a p => check_reachable_aux reach s a (fst p) (snd p)) l ok = true ->
    ok = true /\
    (forall pc i,
     In (pc, i) l ->
     reach!!pc = true ->
     Nodeset.In pc s)).
  induction l; simpl; intros.
  split. auto. intros. destruct H0.
  destruct a as [pc1 i1]. simpl in H.
  exploit IHl; eauto. intros [A B].
  unfold check_reachable_aux in A.
  split. destruct (reach!!pc1). elim (andb_prop _ _ A). auto. auto.
  intros. destruct H0. inv H0. rewrite H1 in A. destruct (andb_prop _ _ A).
  apply Nodeset.mem_2; auto.
  eauto.

  intros pc i. unfold check_reachable. rewrite PTree.fold_spec. intros.
  exploit H; eauto. intros [A B]. eapply B; eauto.
  apply PTree.elements_correct. eauto.
Qed.

Lemma enumerate_complete:
  forall f enum pc i,
  enumerate f = OK enum ->
  f.(LTL.fn_code)!pc = Some i ->
  (reachable f)!!pc = true ->
  In pc enum.
Proof.
  intros until i. unfold enumerate.
  set (reach := reachable f).
  intros. monadInv H.
  generalize EQ0; clear EQ0. caseEq (check_reachable f reach x); intros; inv EQ0.
  exploit check_reachable_correct; eauto. intro.
  exploit nodeset_of_list_correct; eauto. intros [A [B C]].
  rewrite B in H2. destruct H2. elim (Nodeset.empty_1 H2). auto.
Qed.

Lemma enumerate_norepet:
  forall f enum,
  enumerate f = OK enum ->
  list_norepet enum.
Proof.
  intros until enum. unfold enumerate.
  set (reach := reachable f).
  intros. monadInv H.
  generalize EQ0; clear EQ0. caseEq (check_reachable f reach x); intros; inv EQ0.
  exploit nodeset_of_list_correct; eauto. intros [A [B C]]. auto.
Qed.

(** * Properties related to labels *)

(** If labels are globally unique and the Linear code [c] contains
  a subsequence [Llabel lbl :: c1], then [find_label lbl c] returns [c1].
*)

Fixpoint unique_labels (c: code) : Prop :=
  match c with
  | nil => True
  | Llabel lbl :: c => ~(In (Llabel lbl) c) /\ unique_labels c
  | i :: c => unique_labels c
  end.

Lemma find_label_unique:
  forall lbl c1 c2 c3,
  is_tail (Llabel lbl :: c1) c2 ->
  unique_labels c2 ->
  find_label lbl c2 = Some c3 ->
  c1 = c3.
Proof.
  induction c2.
  simpl; intros; discriminate.
  intros c3 TAIL UNIQ. simpl.
  generalize (is_label_correct lbl a). case (is_label lbl a); intro ISLBL.
  subst a. intro. inversion TAIL. congruence.
  elim UNIQ; intros. elim H4. apply is_tail_in with c1; auto.
  inversion TAIL. congruence. apply IHc2. auto.
  destruct a; simpl in UNIQ; tauto.
Qed.

(** Correctness of the [starts_with] test. *)

Lemma starts_with_correct:
  forall lbl c1 c2 c3 s f sp ls m,
  is_tail c1 c2 ->
  unique_labels c2 ->
  starts_with lbl c1 = true ->
  find_label lbl c2 = Some c3 ->
  plus step tge (State s f sp c1 ls m)
             E0 (State s f sp c3 ls m).
Proof.
  induction c1.
  simpl; intros; discriminate.
  simpl starts_with. destruct a; try (intros; discriminate).
  intros.
  apply plus_left with E0 (State s f sp c1 ls m) E0.
  simpl. constructor.
  destruct (peq lbl l).
  subst l. replace c3 with c1. constructor.
  apply find_label_unique with lbl c2; auto.
  apply plus_star.
  apply IHc1 with c2; auto. eapply is_tail_cons_left; eauto.
  traceEq.
Qed.

(** Connection between [find_label] and linearization. *)

Lemma find_label_add_branch:
  forall lbl k s,
  find_label lbl (add_branch s k) = find_label lbl k.
Proof.
  intros. unfold add_branch. destruct (starts_with s k); auto.
Qed.

Lemma find_label_lin_block:
  forall lbl k b,
  find_label lbl (linearize_block b k) = find_label lbl k.
Proof.
  intros lbl k. generalize (find_label_add_branch lbl k); intro.
  induction b; simpl; auto. destruct a; simpl; auto.
  case (starts_with s1 k); simpl; auto.
Qed.

Remark linearize_body_cons:
  forall f pc enum,
  linearize_body f (pc :: enum) =
  match f.(LTL.fn_code)!pc with
  | None => linearize_body f enum
  | Some b => Llabel pc :: linearize_block b (linearize_body f enum)
  end.
Proof.
  intros. unfold linearize_body. rewrite list_fold_right_eq.
  unfold linearize_node. destruct (LTL.fn_code f)!pc; auto.
Qed.

Lemma find_label_lin_rec:
  forall f enum pc b,
  In pc enum ->
  f.(LTL.fn_code)!pc = Some b ->
  exists k, find_label pc (linearize_body f enum) = Some (linearize_block b k).
Proof.
  induction enum; intros.
  elim H.
  rewrite linearize_body_cons.
  destruct (peq a pc).
  subst a. exists (linearize_body f enum).
  rewrite H0. simpl. rewrite peq_true. auto.
  assert (In pc enum). simpl in H. tauto.
  destruct (IHenum pc b H1 H0) as [k FIND].
  exists k. destruct (LTL.fn_code f)!a.
  simpl. rewrite peq_false. rewrite find_label_lin_block. auto. auto.
  auto.
Qed.

Lemma find_label_lin:
  forall f tf pc b,
  transf_function f = OK tf ->
  f.(LTL.fn_code)!pc = Some b ->
  (reachable f)!!pc = true ->
  exists k,
  find_label pc (fn_code tf) = Some (linearize_block b k).
Proof.
  intros. monadInv H. simpl.
  rewrite find_label_add_branch. apply find_label_lin_rec.
  eapply enumerate_complete; eauto. auto.
Qed.

Lemma find_label_lin_inv:
  forall f tf pc b k,
  transf_function f = OK tf ->
  f.(LTL.fn_code)!pc = Some b ->
  (reachable f)!!pc = true ->
  find_label pc (fn_code tf) = Some k ->
  exists k', k = linearize_block b k'.
Proof.
  intros. exploit find_label_lin; eauto. intros [k' FIND].
  exists k'. congruence.
Qed.

(** Unique label property for linearized code. *)

Lemma label_in_add_branch:
  forall lbl s k,
  In (Llabel lbl) (add_branch s k) -> In (Llabel lbl) k.
Proof.
  intros until k; unfold add_branch.
  destruct (starts_with s k); simpl; intuition congruence.
Qed.

Lemma label_in_lin_block:
  forall lbl k b,
  In (Llabel lbl) (linearize_block b k) -> In (Llabel lbl) k.
Proof.
  induction b; simpl; intros. auto.
  destruct a; simpl in H; try (intuition congruence).
  apply label_in_add_branch with s; intuition congruence.
  destruct (starts_with s1 k); simpl in H.
  apply label_in_add_branch with s1; intuition congruence.
  apply label_in_add_branch with s2; intuition congruence.
Qed.

Lemma label_in_lin_rec:
  forall f lbl enum,
  In (Llabel lbl) (linearize_body f enum) -> In lbl enum.
Proof.
  induction enum.
  simpl; auto.
  rewrite linearize_body_cons. destruct (LTL.fn_code f)!a.
  simpl. intros [A|B]. left; congruence.
  right. apply IHenum. eapply label_in_lin_block; eauto.
  intro; right; auto.
Qed.

Lemma unique_labels_add_branch:
  forall lbl k,
  unique_labels k -> unique_labels (add_branch lbl k).
Proof.
  intros; unfold add_branch.
  destruct (starts_with lbl k); simpl; intuition.
Qed.

Lemma unique_labels_lin_block:
  forall k b,
  unique_labels k -> unique_labels (linearize_block b k).
Proof.
  induction b; intros; simpl. auto.
  destruct a; auto; try (apply unique_labels_add_branch; auto).
  case (starts_with s1 k); simpl; apply unique_labels_add_branch; auto.
Qed.

Lemma unique_labels_lin_rec:
  forall f enum,
  list_norepet enum ->
  unique_labels (linearize_body f enum).
Proof.
  induction enum.
  simpl; auto.
  rewrite linearize_body_cons.
  intro. destruct (LTL.fn_code f)!a.
  simpl. split. red. intro. inversion H. elim H3.
  apply label_in_lin_rec with f.
  apply label_in_lin_block with b. auto.
  apply unique_labels_lin_block. apply IHenum. inversion H; auto.
  apply IHenum. inversion H; auto.
Qed.

Lemma unique_labels_transf_function:
  forall f tf,
  transf_function f = OK tf ->
  unique_labels (fn_code tf).
Proof.
  intros. monadInv H. simpl.
  apply unique_labels_add_branch.
  apply unique_labels_lin_rec. eapply enumerate_norepet; eauto.
Qed.

(** Correctness of [add_branch]. *)

Lemma is_tail_find_label:
  forall lbl c2 c1,
  find_label lbl c1 = Some c2 -> is_tail c2 c1.
Proof.
  induction c1; simpl.
  intros; discriminate.
  case (is_label lbl a). intro. injection H; intro. subst c2.
  constructor. constructor.
  intro. constructor. auto.
Qed.

Lemma is_tail_add_branch:
  forall lbl c1 c2, is_tail (add_branch lbl c1) c2 -> is_tail c1 c2.
Proof.
  intros until c2. unfold add_branch. destruct (starts_with lbl c1).
  auto. eauto with coqlib.
Qed.

Lemma is_tail_lin_block:
  forall b c1 c2,
  is_tail (linearize_block b c1) c2 -> is_tail c1 c2.
Proof.
  induction b; simpl; intros.
  auto.
  destruct a; eauto with coqlib.
  eapply is_tail_add_branch; eauto.
  destruct (starts_with s1 c1); eapply is_tail_add_branch; eauto with coqlib.
Qed.

Lemma add_branch_correct:
  forall lbl c k s f tf sp ls m,
  transf_function f = OK tf ->
  is_tail k tf.(fn_code) ->
  find_label lbl tf.(fn_code) = Some c ->
  plus step tge (State s tf sp (add_branch lbl k) ls m)
             E0 (State s tf sp c ls m).
Proof.
  intros. unfold add_branch.
  caseEq (starts_with lbl k); intro SW.
  eapply starts_with_correct; eauto.
  eapply unique_labels_transf_function; eauto.
  apply plus_one. apply exec_Lgoto. auto.
Qed.

(** * Correctness of linearization *)

(** The proof of semantic preservation is a simulation argument of the "star" kind:
<<
           st1 --------------- st2
            |                   |
           t|                  t| + or ( 0 \/ |st1'| < |st1| )
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant (horizontal lines above) is the [match_states]
  predicate defined below.  It captures the fact that the flow
  of data is the same in the source and linearized codes.
  Moreover, whenever the source state is at node [pc] in its
  control-flow graph, the transformed state is at a code
  sequence [c] that starts with the label [pc]. *)

Inductive match_stackframes: LTL.stackframe -> Linear.stackframe -> Prop :=
  | match_stackframe_intro:
      forall f sp bb ls tf c,
      transf_function f = OK tf ->
      (forall pc, In pc (successors_block bb) -> (reachable f)!!pc = true) ->
      is_tail c tf.(fn_code) ->
      match_stackframes
        (LTL.Stackframe f sp ls bb)
        (Linear.Stackframe tf sp ls (linearize_block bb c)).

Inductive match_states: LTL.state -> Linear.state -> Prop :=
  | match_states_add_branch:
      forall s f sp pc ls m tf ts c
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: transf_function f = OK tf)
        (REACH: (reachable f)!!pc = true)
        (TAIL: is_tail c tf.(fn_code)),
      match_states (LTL.State s f sp pc ls m)
                   (Linear.State ts tf sp (add_branch pc c) ls m)
  | match_states_cond_taken:
      forall s f sp pc ls m tf ts cond args c
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: transf_function f = OK tf)
        (REACH: (reachable f)!!pc = true)
        (JUMP: eval_condition cond (reglist ls args) m = Some true),
      match_states (LTL.State s f sp pc (undef_regs (destroyed_by_cond cond) ls) m)
                   (Linear.State ts tf sp (Lcond cond args pc :: c) ls m)
  | match_states_jumptable:
      forall s f sp pc ls m tf ts arg tbl c n
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: transf_function f = OK tf)
        (REACH: (reachable f)!!pc = true)
        (ARG: ls (R arg) = Vint n)
        (JUMP: list_nth_z tbl (Int.unsigned n) = Some pc),
      match_states (LTL.State s f sp pc (undef_regs destroyed_by_jumptable ls) m)
                   (Linear.State ts tf sp (Ljumptable arg tbl :: c) ls m)
  | match_states_block:
      forall s f sp bb ls m tf ts c
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: transf_function f = OK tf)
        (REACH: forall pc, In pc (successors_block bb) -> (reachable f)!!pc = true)
        (TAIL: is_tail c tf.(fn_code)),
      match_states (LTL.Block s f sp bb ls m)
                   (Linear.State ts tf sp (linearize_block bb c) ls m)
  | match_states_call:
      forall s f ls m tf ts,
      list_forall2 match_stackframes s ts ->
      transf_fundef f = OK tf ->
      match_states (LTL.Callstate s f ls m)
                   (Linear.Callstate ts tf ls m)
  | match_states_return:
      forall s ls m ts,
      list_forall2 match_stackframes s ts ->
      match_states (LTL.Returnstate s ls m)
                   (Linear.Returnstate ts ls m).

Definition measure (S: LTL.state) : nat :=
  match S with
  | LTL.State s f sp pc ls m => 0%nat
  | LTL.Block s f sp bb ls m => 1%nat
  | _ => 0%nat
  end.

Remark match_parent_locset:
  forall s ts, list_forall2 match_stackframes s ts -> parent_locset ts = LTL.parent_locset s.
Proof.
  induction 1; simpl. auto. inv H; auto.
Qed.

Theorem transf_step_correct:
  forall s1 t s2, LTL.step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  (exists s2', plus Linear.step tge s1' t s2' /\ match_states s2 s2')
  \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat.
Proof.
  induction 1; intros; try (inv MS).

  (* start of block, at an [add_branch] *)
  exploit find_label_lin; eauto. intros [k F].
  left; econstructor; split.
  eapply add_branch_correct; eauto.
  econstructor; eauto.
  intros; eapply reachable_successors; eauto.
  eapply is_tail_lin_block; eauto. eapply is_tail_find_label; eauto.

  (* start of block, target of an [Lcond] *)
  exploit find_label_lin; eauto. intros [k F].
  left; econstructor; split.
  apply plus_one. eapply exec_Lcond_true; eauto.
  econstructor; eauto.
  intros; eapply reachable_successors; eauto.
  eapply is_tail_lin_block; eauto. eapply is_tail_find_label; eauto.

  (* start of block, target of an [Ljumptable] *)
  exploit find_label_lin; eauto. intros [k F].
  left; econstructor; split.
  apply plus_one. eapply exec_Ljumptable; eauto.
  econstructor; eauto.
  intros; eapply reachable_successors; eauto.
  eapply is_tail_lin_block; eauto. eapply is_tail_find_label; eauto.

  (* Lop *)
  left; econstructor; split. simpl.
  apply plus_one. econstructor; eauto.
  instantiate (1 := v); rewrite <- H; apply eval_operation_preserved.
  exact symbols_preserved.
  econstructor; eauto.

  (* Lload *)
  left; econstructor; split. simpl.
  apply plus_one. econstructor.
  instantiate (1 := a). rewrite <- H; apply eval_addressing_preserved.
  exact symbols_preserved. eauto. eauto.
  econstructor; eauto.

  (* Lgetstack *)
  left; econstructor; split. simpl.
  apply plus_one. econstructor; eauto.
  econstructor; eauto.

  (* Lsetstack *)
  left; econstructor; split. simpl.
  apply plus_one. econstructor; eauto.
  econstructor; eauto.

  (* Lstore *)
  left; econstructor; split. simpl.
  apply plus_one. econstructor.
  instantiate (1 := a). rewrite <- H; apply eval_addressing_preserved.
  exact symbols_preserved. eauto. eauto.
  econstructor; eauto.

  (* Lcall *)
  exploit find_function_translated; eauto. intros [tfd [A B]].
  left; econstructor; split. simpl.
  apply plus_one. econstructor; eauto.
  symmetry; eapply sig_preserved; eauto.
  econstructor; eauto. constructor; auto. econstructor; eauto.

  (* Ltailcall *)
  exploit find_function_translated; eauto. intros [tfd [A B]].
  left; econstructor; split. simpl.
  apply plus_one. econstructor; eauto.
  rewrite (match_parent_locset _ _ STACKS). eauto.
  symmetry; eapply sig_preserved; eauto.
  rewrite (stacksize_preserved _ _ TRF); eauto.
  rewrite (match_parent_locset _ _ STACKS).
  econstructor; eauto.

  (* Lbuiltin *)
  left; econstructor; split. simpl.
  apply plus_one. eapply exec_Lbuiltin; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.

  (* Lbranch *)
  assert ((reachable f)!!pc = true). apply REACH; simpl; auto.
  right; split. simpl; omega. split. auto. simpl. econstructor; eauto.

  (* Lcond *)
  assert (REACH1: (reachable f)!!pc1 = true) by (apply REACH; simpl; auto).
  assert (REACH2: (reachable f)!!pc2 = true) by (apply REACH; simpl; auto).
  simpl linearize_block.
  destruct (starts_with pc1 c).
  (* branch if cond is false *)
  assert (DC: destroyed_by_cond (negate_condition cond) = destroyed_by_cond cond).
    destruct cond; reflexivity.
  destruct b.
  (* cond is true: no branch *)
  left; econstructor; split.
  apply plus_one. eapply exec_Lcond_false.
  rewrite eval_negate_condition. rewrite H. auto. eauto.
  rewrite DC. econstructor; eauto.
  (* cond is false: branch is taken *)
  right; split. simpl; omega. split. auto.  rewrite <- DC. econstructor; eauto.
  rewrite eval_negate_condition. rewrite H. auto.
  (* branch if cond is true *)
  destruct b.
  (* cond is true: branch is taken *)
  right; split. simpl; omega. split. auto. econstructor; eauto.
  (* cond is false: no branch *)
  left; econstructor; split.
  apply plus_one. eapply exec_Lcond_false. eauto. eauto.
  econstructor; eauto.

  (* Ljumptable *)
  assert (REACH': (reachable f)!!pc = true).
    apply REACH. simpl. eapply list_nth_z_in; eauto.
  right; split. simpl; omega. split. auto. econstructor; eauto.

  (* Lreturn *)
  left; econstructor; split.
  simpl. apply plus_one. econstructor; eauto.
  rewrite (stacksize_preserved _ _ TRF). eauto.
  rewrite (match_parent_locset _ _ STACKS). econstructor; eauto.

  (* internal functions *)
  assert (REACH: (reachable f)!!(LTL.fn_entrypoint f) = true).
    apply reachable_entrypoint.
  monadInv H7.
  left; econstructor; split.
  apply plus_one. eapply exec_function_internal; eauto.
  rewrite (stacksize_preserved _ _ EQ). eauto.
  generalize EQ; intro EQ'; monadInv EQ'. simpl.
  econstructor; eauto. simpl. eapply is_tail_add_branch. constructor.

  (* external function *)
  monadInv H8. left; econstructor; split.
  apply plus_one. eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.

  (* return *)
  inv H3. inv H1.
  left; econstructor; split.
  apply plus_one. econstructor.
  econstructor; eauto.
Qed.

Lemma transf_initial_states:
  forall st1, LTL.initial_state prog st1 ->
  exists st2, Linear.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists (Callstate nil tf (Locmap.init Vundef) m0); split.
  econstructor; eauto. eapply (Genv.init_mem_transf_partial TRANSF); eauto.
  rewrite (match_program_main TRANSF).
  rewrite symbols_preserved. eauto.
  rewrite <- H3. apply sig_preserved. auto.
  constructor. constructor. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> LTL.final_state st1 r -> Linear.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H5. econstructor; eauto.
Qed.

Theorem transf_program_correct:
  forward_simulation (LTL.semantics prog) (Linear.semantics tprog).
Proof.
  eapply forward_simulation_star.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact transf_step_correct.
Qed.

End LINEARIZATION.

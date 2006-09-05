(** Correctness proof for code linearization *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import Linear.
Require Import Linearize.
Require Import Lattice.

Section LINEARIZATION.

Variable prog: LTL.program.
Let tprog := transf_program prog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof (@Genv.find_funct_transf _ _ _ transf_fundef prog).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof (@Genv.find_funct_ptr_transf _ _ _ transf_fundef prog).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (@Genv.find_symbol_transf _ _ _ transf_fundef prog).

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = LTL.funsig f.
Proof.
  destruct f; reflexivity.
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
  eapply DS.fixpoint_entry. eexact A. auto with coqlib.
  unfold LBoolean.ge in H. tauto.
  intros. apply PMap.gi.
Qed.

(** The successors of a reachable basic block are reachable. *)

Lemma reachable_successors:
  forall f pc pc',
  f.(LTL.fn_code)!pc <> None ->
  In pc' (successors f pc) ->
  (reachable f)!!pc = true ->
  (reachable f)!!pc' = true.
Proof.
  intro f. unfold reachable.
  caseEq (reachable_aux f).
  unfold reachable_aux. intro reach; intros.
  assert (LBoolean.ge reach!!pc' reach!!pc).
  change (reach!!pc) with ((fun pc r => r) pc (reach!!pc)).
  eapply DS.fixpoint_solution. eexact H.
  elim (fn_code_wf f pc); intro. auto. contradiction.
  auto. 
  elim H3; intro. congruence. auto.
  intros. apply PMap.gi.
Qed.

(* If we have a valid LTL transition from [pc] to [pc'], and
  [pc] is reachable, then [pc'] is reachable. *)

Lemma reachable_correct_1:
  forall f sp pc rs m t pc' rs' m' b,
  f.(LTL.fn_code)!pc = Some b ->
  exec_block ge sp b rs m t (Cont pc') rs' m' ->
  (reachable f)!!pc = true ->
  (reachable f)!!pc' = true.
Proof.
  intros. apply reachable_successors with pc; auto.
  congruence.
  eapply successors_correct; eauto.
Qed.

Lemma reachable_correct_2:
  forall c sp pc rs m t out rs' m',
  exec_blocks ge c sp pc rs m t out rs' m' ->  
  forall f pc',
  c = f.(LTL.fn_code) ->
  out = Cont pc' ->
  (reachable f)!!pc = true ->
  (reachable f)!!pc' = true.
Proof.
  induction 1; intros.
  congruence.
  eapply reachable_correct_1. rewrite <- H1; eauto. 
  subst out; eauto. auto.
  auto.
Qed.

(** * Properties of node enumeration *)

(** An enumeration of CFG nodes is correct if the following conditions hold:
- All nodes for reachable basic blocks must be in the list.
- The function entry point is the first element in the list.
- The list is without repetition (so that no code duplication occurs).

We prove that our [enumerate] function satisfies all three. *)

Lemma enumerate_complete:
  forall f pc i,
  f.(LTL.fn_code)!pc = Some i ->
  (reachable f)!!pc = true ->
  In pc (enumerate f).
Proof.
  intros. 
  assert (forall p, 
    Plt p (Psucc f.(fn_entrypoint)) ->
    (reachable f)!!p = true ->
    In p (enumerate f)).
  unfold enumerate. pattern (Psucc (fn_entrypoint f)).
  apply positive_Peano_ind. 
  intros. compute in H1. destruct p; discriminate. 
  intros. rewrite positive_rec_succ. elim (Plt_succ_inv _ _ H2); intro.
  case (reachable f)!!x. apply in_cons. auto. auto.
  subst x. rewrite H3. apply in_eq. 
  elim (LTL.fn_code_wf f pc); intro. auto. congruence.
Qed. 

Lemma enumerate_head:
  forall f, exists l, enumerate f = f.(LTL.fn_entrypoint) :: l.
Proof.
  intro. unfold enumerate. rewrite positive_rec_succ. 
  rewrite reachable_entrypoint.
  exists (positive_rec (list node) nil
    (fun (pc : positive) (nodes : list node) =>
      if (reachable f) !! pc then pc :: nodes else nodes) 
    (fn_entrypoint f) ).
  auto.
Qed.

Lemma enumerate_norepet:
  forall f, list_norepet (enumerate f).
Proof.
  intro. 
  unfold enumerate. pattern (Psucc (fn_entrypoint f)).
  apply positive_Peano_ind.  
  rewrite positive_rec_base. constructor.
  intros. rewrite positive_rec_succ.
  case (reachable f)!!x. auto.
  constructor. 
  assert (forall y,
    In y (positive_rec
     (list node) nil
     (fun (pc : positive) (nodes : list node) =>
      if (reachable f) !! pc then pc :: nodes else nodes) x) ->
    Plt y x).
    pattern x. apply positive_Peano_ind. 
    rewrite positive_rec_base. intros. elim H0.
    intros until y. rewrite positive_rec_succ. 
    case (reachable f)!!x0. 
    simpl. intros [A|B].
    subst x0. apply Plt_succ.
    apply Plt_trans_succ. auto. 
    intro. apply Plt_trans_succ. auto.
  red; intro. generalize (H0 x H1). exact (Plt_strict x). auto.
  auto.
Qed.

(** * Correctness of the cleanup pass *)

(** If labels are globally unique and the Linear code [c] contains
  a subsequence [Llabel lbl :: c1], [find_label lbl c] returns [c1].
*)

Fixpoint unique_labels (c: code) : Prop :=
  match c with
  | nil => True
  | Llabel lbl :: c => ~(In (Llabel lbl) c) /\ unique_labels c
  | i :: c => unique_labels c
  end.

Inductive is_tail: code -> code -> Prop :=
  | is_tail_refl:
      forall c, is_tail c c
  | is_tail_cons:
      forall i c1 c2, is_tail c1 c2 -> is_tail c1 (i :: c2).

Lemma is_tail_in:
  forall i c1 c2, is_tail (i :: c1) c2 -> In i c2.
Proof.
  induction c2; simpl; intros.
  inversion H.
  inversion H. tauto. right; auto.
Qed.

Lemma is_tail_cons_left:
  forall i c1 c2, is_tail (i :: c1) c2 -> is_tail c1 c2.
Proof.
  induction c2; intros; inversion H.
  constructor. constructor. constructor. auto. 
Qed.

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
  forall lbl c1 c2 c3 f sp ls m,
  is_tail c1 c2 ->
  unique_labels c2 ->
  starts_with lbl c1 = true ->
  find_label lbl c2 = Some c3 ->
  exec_instrs tge f sp (cleanup_code c1) ls m 
                    E0 (cleanup_code c3) ls m.
Proof.
  induction c1.
  simpl; intros; discriminate.
  simpl starts_with. destruct a; try (intros; discriminate).
  intros. apply exec_trans with E0 (cleanup_code c1) ls m E0.
  simpl. 
  constructor. constructor. 
  destruct (peq lbl l).
  subst l. replace c3 with c1. constructor.
  apply find_label_unique with lbl c2; auto.
  apply IHc1 with c2; auto. eapply is_tail_cons_left; eauto.
  traceEq.
Qed.

(** Code cleanup preserves the labeling of the code. *)

Lemma find_label_cleanup_code:
  forall lbl c c',
  find_label lbl c = Some c' ->
  find_label lbl (cleanup_code c) = Some (cleanup_code c').
Proof.
  induction c.  
  simpl. intros; discriminate.
  generalize (is_label_correct lbl a). 
  simpl find_label. case (is_label lbl a); intro.
  subst a. intros. injection H; intros. subst c'. 
  simpl. rewrite peq_true. auto.
  intros. destruct a; auto. 
  simpl. rewrite peq_false. auto.
  congruence. 
  case (starts_with l c). auto. simpl. auto.
Qed.

(** One transition in the original Linear code corresponds to zero
  or one transitions in the cleaned-up code. *)

Lemma cleanup_code_correct_1:
  forall f sp c1 ls1 m1 t c2 ls2 m2,
  exec_instr tge f sp c1 ls1 m1 t c2 ls2 m2 ->
  is_tail c1 f.(fn_code) ->
  unique_labels f.(fn_code) ->
  exec_instrs tge (cleanup_function f) sp 
                       (cleanup_code c1) ls1 m1
                     t (cleanup_code c2) ls2 m2.
Proof.
  induction 1; simpl; intros;
  try (apply exec_one; econstructor; eauto; fail).
  (* goto *)
  caseEq (starts_with lbl b); intro SW.
  eapply starts_with_correct; eauto.
  eapply is_tail_cons_left; eauto.
  constructor. constructor. 
  unfold cleanup_function; simpl. 
  apply find_label_cleanup_code. auto.
  (* cond, taken *)
  constructor. apply exec_Lcond_true. auto.
  unfold cleanup_function; simpl. 
  apply find_label_cleanup_code. auto.
  (* cond, not taken *)
  constructor. apply exec_Lcond_false. auto.
Qed. 

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

Lemma is_tail_exec_instr:
  forall f sp c1 ls1 m1 t c2 ls2 m2,
  exec_instr tge f sp c1 ls1 m1 t c2 ls2 m2 ->
  is_tail c1 f.(fn_code) -> is_tail c2 f.(fn_code).
Proof.
  induction 1; intros;
  try (eapply is_tail_cons_left; eauto; fail).
  eapply is_tail_find_label; eauto.
  eapply is_tail_find_label; eauto.
Qed.

Lemma is_tail_exec_instrs:
  forall f sp c1 ls1 m1 t c2 ls2 m2,
  exec_instrs tge f sp c1 ls1 m1 t c2 ls2 m2 ->
  is_tail c1 f.(fn_code) -> is_tail c2 f.(fn_code).
Proof.
  induction 1; intros.
  auto.
  eapply is_tail_exec_instr; eauto.
  auto.
Qed.

(** Zero, one or several transitions in the original Linear code correspond
  to zero, one or several transitions in the cleaned-up code. *)

Lemma cleanup_code_correct_2:
  forall f sp c1 ls1 m1 t c2 ls2 m2,
  exec_instrs tge f sp c1 ls1 m1 t c2 ls2 m2 ->
  is_tail c1 f.(fn_code) ->
  unique_labels f.(fn_code) ->
  exec_instrs tge (cleanup_function f) sp 
                       (cleanup_code c1) ls1 m1
                     t (cleanup_code c2) ls2 m2.
Proof.
  induction 1; simpl; intros.
  apply exec_refl.
  eapply cleanup_code_correct_1; eauto.
  apply exec_trans with t1 (cleanup_code b2) rs2 m2 t2.
  auto. 
  apply IHexec_instrs2; auto.
  eapply is_tail_exec_instrs; eauto.
  auto.
Qed.

Lemma cleanup_function_correct:
  forall f ls1 m1 t ls2 m2,
  exec_function tge (Internal f) ls1 m1 t ls2 m2 ->
  unique_labels f.(fn_code) ->
  exec_function tge (Internal (cleanup_function f)) ls1 m1 t ls2 m2. 
Proof.
  intros. inversion H; subst.
  generalize (cleanup_code_correct_2 _ _ _ _ _ _ _ _ _ H3 (is_tail_refl _) H0).
  simpl. intro.
  econstructor; eauto.
Qed.

(** * Properties of linearized code *)

(** We now state useful properties of the Linear code generated by
  the naive LTL-to-Linear translation. *)

(** Connection between [find_label] and linearization. *)

Lemma find_label_lin_block:
  forall lbl k b,
  find_label lbl (linearize_block b k) = find_label lbl k.
Proof.
  induction b; simpl; auto.
  case (starts_with n k); reflexivity.
Qed.

Lemma find_label_lin_rec:
  forall f enum pc b,
  In pc enum ->
  f.(LTL.fn_code)!pc = Some b ->
  exists k,
  find_label pc (linearize_body f enum) = Some (linearize_block b k).
Proof.
  induction enum; intros.
  elim H.
  case (peq a pc); intro.
  subst a. exists (linearize_body f enum).
  simpl. rewrite H0. simpl. rewrite peq_true. auto.
  assert (In pc enum). simpl in H. tauto.
  elim (IHenum pc b H1 H0). intros k FIND.
  exists k. simpl. destruct (LTL.fn_code f)!a. 
  simpl. rewrite peq_false. rewrite find_label_lin_block. auto. auto.
  auto.
Qed.

Lemma find_label_lin:
  forall f pc b,
  f.(LTL.fn_code)!pc = Some b ->
  (reachable f)!!pc = true ->
  exists k,
  find_label pc (fn_code (linearize_function f)) = Some (linearize_block b k).
Proof.
  intros. unfold linearize_function; simpl. apply find_label_lin_rec.
  eapply enumerate_complete; eauto. auto.
Qed.

(** Unique label property for linearized code. *)

Lemma label_in_lin_block:
  forall lbl k b,
  In (Llabel lbl) (linearize_block b k) -> In (Llabel lbl) k.
Proof.
  induction b; simpl; try (intuition congruence).
  case (starts_with n k); simpl; intuition congruence.
Qed.

Lemma label_in_lin_rec:
  forall f lbl enum,
  In (Llabel lbl) (linearize_body f enum) -> In lbl enum.
Proof.
  induction enum.
  simpl; auto.
  simpl. destruct (LTL.fn_code f)!a. 
  simpl. intros [A|B]. left; congruence. 
  right. apply IHenum. eapply label_in_lin_block; eauto.
  intro; right; auto.
Qed.

Lemma unique_labels_lin_block:
  forall k b,
  unique_labels k -> unique_labels (linearize_block b k).
Proof.
  induction b; simpl; auto.
  case (starts_with n k); simpl; auto.
Qed.

Lemma unique_labels_lin_rec:
  forall f enum,
  list_norepet enum ->
  unique_labels (linearize_body f enum).
Proof.
  induction enum.
  simpl; auto.
  intro. simpl. destruct (LTL.fn_code f)!a. 
  simpl. split. red. intro. inversion H. elim H3.
  apply label_in_lin_rec with f. 
  apply label_in_lin_block with b. auto.
  apply unique_labels_lin_block. apply IHenum. inversion H; auto.
  apply IHenum. inversion H; auto.
Qed.

Lemma unique_labels_lin_function:
  forall f,
  unique_labels (fn_code (linearize_function f)).
Proof.
  intros. unfold linearize_function; simpl.
  apply unique_labels_lin_rec. apply enumerate_norepet. 
Qed.

(** * Correctness of linearization *)

(** The outcome of an LTL [exec_block] or [exec_blocks] execution
  is valid if it corresponds to a reachable, existing basic block.
  All outcomes occurring in an LTL program execution are actually
  valid, but we will prove that along with the main simulation proof. *)

Definition valid_outcome (f: LTL.function) (out: outcome) :=
  match out with
  | Cont s =>
      (reachable f)!!s = true /\ exists b, f.(LTL.fn_code)!s = Some b
  | Return => True
  end.

(** Auxiliary lemma used to establish the [valid_outcome] property. *)

Lemma exec_blocks_valid_outcome:
  forall c sp pc ls1 m1 t out ls2 m2,
  exec_blocks ge c sp pc ls1 m1 t out ls2 m2 ->
  forall f,
  c = f.(LTL.fn_code) ->
  (reachable f)!!pc = true ->
  valid_outcome f out ->
  valid_outcome f (Cont pc).
Proof.
  induction 1.
  auto.
  intros. simpl. split. auto. exists b. congruence. 
  intros. apply IHexec_blocks1. auto. auto.
  apply IHexec_blocks2. auto. 
  eapply reachable_correct_2. eexact H. auto. auto. auto.
  auto.
Qed.

(** Correspondence between an LTL outcome and a fragment of generated
  Linear code. *)

Inductive cont_for_outcome: LTL.function -> outcome -> code -> Prop :=
  | co_return:
      forall f k,
      cont_for_outcome f Return (Lreturn :: k)
  | co_goto:
      forall f s k,
      find_label s (linearize_function f).(fn_code) = Some k ->
      cont_for_outcome f (Cont s) k.

(** The simulation properties used in the inductive proof.
  They are parameterized by an LTL execution, and state
  that a matching execution is possible in the generated Linear code. *)

Definition exec_instr_prop 
  (sp: val) (b1: block) (ls1: locset) (m1: mem)
  (t: trace) (b2: block) (ls2: locset) (m2: mem) : Prop :=
  forall f k,
  exec_instr tge (linearize_function f) sp
                 (linearize_block b1 k) ls1 m1
               t (linearize_block b2 k) ls2 m2.

Definition exec_instrs_prop
  (sp: val) (b1: block) (ls1: locset) (m1: mem)
  (t: trace) (b2: block) (ls2: locset) (m2: mem) : Prop :=
  forall f k,
  exec_instrs tge (linearize_function f) sp
                  (linearize_block b1 k) ls1 m1
                t (linearize_block b2 k) ls2 m2.

Definition exec_block_prop
  (sp: val) (b: block) (ls1: locset) (m1: mem) 
  (t: trace) (out: outcome) (ls2: locset) (m2: mem): Prop :=
  forall f k,
  valid_outcome f out ->
  exists k',
  exec_instrs tge (linearize_function f) sp
                  (linearize_block b k) ls1 m1
                t k' ls2 m2
  /\ cont_for_outcome f out k'.

Definition exec_blocks_prop
  (c: LTL.code) (sp: val) (pc: node) (ls1: locset) (m1: mem) 
         (t: trace) (out: outcome) (ls2: locset) (m2: mem): Prop :=
  forall f k,
  c = f.(LTL.fn_code) ->
  (reachable f)!!pc = true ->
  find_label pc (fn_code (linearize_function f)) = Some k ->
  valid_outcome f out ->
  exists k',
  exec_instrs tge (linearize_function f) sp
                  k ls1 m1
                t k' ls2 m2
  /\ cont_for_outcome f out k'.

Definition exec_function_prop
  (f: LTL.fundef) (ls1: locset) (m1: mem) (t: trace)
  (ls2: locset) (m2: mem): Prop :=
  exec_function tge (transf_fundef f) ls1 m1 t ls2 m2.

Scheme exec_instr_ind5 := Minimality for LTL.exec_instr Sort Prop
  with exec_instrs_ind5 := Minimality for LTL.exec_instrs Sort Prop
  with exec_block_ind5 := Minimality for LTL.exec_block Sort Prop
  with exec_blocks_ind5 := Minimality for LTL.exec_blocks Sort Prop
  with exec_function_ind5 := Minimality for LTL.exec_function Sort Prop.

(** The obligatory proof by structural induction on the LTL evaluation
  derivation. *)

Lemma transf_function_correct:
  forall f ls1 m1 t ls2 m2,
  LTL.exec_function ge f ls1 m1 t ls2 m2 ->
  exec_function_prop f ls1 m1 t ls2 m2.
Proof.
  apply (exec_function_ind5 ge
           exec_instr_prop
           exec_instrs_prop
           exec_block_prop
           exec_blocks_prop
           exec_function_prop);
  intros; red; intros; simpl.
  (* getstack *)
  constructor.
  (* setstack *)
  constructor.
  (* op *)
  constructor. rewrite <- H. apply eval_operation_preserved.
  exact symbols_preserved.
  (* load *)
  apply exec_Lload with a. 
  rewrite <- H. apply eval_addressing_preserved.
  exact symbols_preserved.
  auto.
  (* store *)
  apply exec_Lstore with a.
  rewrite <- H. apply eval_addressing_preserved.
  exact symbols_preserved.
  auto.
  (* call *)
  apply exec_Lcall with (transf_fundef f).
  generalize H. destruct ros; simpl.
  intro; apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  intro; apply function_ptr_translated; auto. congruence.
  generalize (sig_preserved f). congruence.
  apply H2. 
  (* alloc *)
  eapply exec_Lalloc; eauto. 
  (* instr_refl *)
  apply exec_refl.
  (* instr_one *)
  apply exec_one. apply H0. 
  (* instr_trans *)
  apply exec_trans with t1 (linearize_block b2 k) rs2 m2 t2.
  apply H0. apply H2. auto.
  (* goto *)
  elim H1. intros REACH [b2 AT2]. 
  generalize (H0 f k). simpl. intro.
  elim (find_label_lin f s b2 AT2 REACH). intros k2 FIND.
  exists (linearize_block b2 k2).
  split. 
  eapply exec_trans. eexact H2. constructor. constructor. auto. traceEq.
  constructor. auto. 
  (* cond, true *)
  elim H2. intros REACH [b2 AT2]. 
  elim (find_label_lin f ifso b2 AT2 REACH). intros k2 FIND.
  exists (linearize_block b2 k2).
  split.
  generalize (H0 f k). simpl. 
  case (starts_with ifso k); intro.
  eapply exec_trans. eexact H3. 
  eapply exec_trans. apply exec_one. apply exec_Lcond_false.
  change false with (negb true). apply eval_negate_condition. auto.
  apply exec_one. apply exec_Lgoto. auto. reflexivity. traceEq.
  eapply exec_trans. eexact H3. 
  apply exec_one. apply exec_Lcond_true.
  auto. auto. traceEq.
  constructor; auto.
  (* cond, false *)
  elim H2. intros REACH [b2 AT2]. 
  elim (find_label_lin f ifnot b2 AT2 REACH). intros k2 FIND.
  exists (linearize_block b2 k2).
  split.
  generalize (H0 f k). simpl. 
  case (starts_with ifso k); intro.
  eapply exec_trans. eexact H3. 
  apply exec_one. apply exec_Lcond_true. 
  change true with (negb false). apply eval_negate_condition. auto.
  auto. traceEq.
  eapply exec_trans. eexact H3.
  eapply exec_trans. apply exec_one. apply exec_Lcond_false. auto.
  apply exec_one. apply exec_Lgoto. auto. reflexivity. traceEq.
  constructor; auto.
  (* return *)
  exists (Lreturn :: k). split. 
  exact (H0 f k). constructor.
  (* refl blocks *)
  exists k. split. apply exec_refl. constructor. auto.
  (* one blocks *)
  subst c. elim (find_label_lin f pc b H H3). intros k' FIND.
  assert (k = linearize_block b k'). congruence. subst k.
  elim (H1 f k' H5). intros k'' [EXEC CFO].
  exists k''. tauto.
  (* trans blocks *)
  assert ((reachable f)!!pc2 = true).
    eapply reachable_correct_2. eexact H. auto. auto. auto.
  assert (valid_outcome f (Cont pc2)).
    eapply exec_blocks_valid_outcome; eauto.
  generalize (H0 f k H4 H5 H6 H9). intros [k1 [EX1 CFO2]].
  inversion CFO2. 
  generalize (H2 f k1 H4 H8 H12 H7). intros [k2 [EX2 CFO3]].
  exists k2. split. eapply exec_trans; eauto. auto.
  (* internal function -- TA-DA! *)
  assert (REACH0: (reachable f)!!(fn_entrypoint f) = true).
    apply reachable_entrypoint.
  assert (VO2: valid_outcome f Return). simpl; auto.
  assert (VO1: valid_outcome f (Cont (fn_entrypoint f))).
    eapply exec_blocks_valid_outcome; eauto.
  assert (exists k, fn_code (linearize_function f) = Llabel f.(fn_entrypoint) :: k).
    unfold linearize_function; simpl. 
    elim (enumerate_head f). intros tl EN. rewrite EN. 
    simpl. elim VO1. intros REACH [b EQ]. rewrite EQ. 
    exists (linearize_block b (linearize_body f tl)). auto.
  elim H2; intros k EQ.
  assert (find_label (fn_entrypoint f) (fn_code (linearize_function f)) =
            Some k).
    rewrite EQ. simpl. rewrite peq_true. auto.
  generalize (H1 f k (refl_equal _) REACH0 H3 VO2). 
  intros [k' [EX CO]].
  inversion CO. subst k'. 
  unfold transf_function. apply cleanup_function_correct.
  econstructor. eauto. rewrite EQ. eapply exec_trans.
  apply exec_one. constructor. eauto. traceEq.
  apply unique_labels_lin_function.
  (* external function *)
  econstructor; eauto.
Qed.

End LINEARIZATION.

Theorem transf_program_correct:
  forall (p: LTL.program) (t: trace) (r: val),
  LTL.exec_program p t r ->
  Linear.exec_program (transf_program p) t r.
Proof.
  intros p t r [b [f [ls [m [FIND1 [FIND2 [SIG [EX RES]]]]]]]].
  red. exists b; exists (transf_fundef f); exists ls; exists m.
  split. change (prog_main (transf_program p)) with (prog_main p).
  rewrite symbols_preserved; auto.
  split. apply function_ptr_translated. auto.
  split. generalize (sig_preserved f); congruence.
  split. apply transf_function_correct. 
  unfold transf_program. rewrite Genv.init_mem_transf. auto.
  rewrite sig_preserved. exact RES.
Qed.


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

(** Correctness proof for common subexpression elimination. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Errors.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import RTLtyping.
Require Import Kildall.
Require Import CombineOp.
Require Import CombineOpproof.
Require Import CSE.

(** * Semantic properties of value numberings *)

(** ** Well-formedness of numberings *)

(** A numbering is well-formed if all registers mentioned in equations
  are less than the ``next'' register number given in the numbering.
  This guarantees that the next register is fresh with respect to
  the equations. *)

Definition wf_rhs (next: valnum) (rh: rhs) : Prop :=
  match rh with
  | Op op vl => forall v, In v vl -> Plt v next
  | Load chunk addr vl => forall v, In v vl -> Plt v next
  end.

Definition wf_equation (next: valnum) (vr: valnum) (rh: rhs) : Prop :=
  Plt vr next /\ wf_rhs next rh.

Inductive wf_numbering (n: numbering) : Prop :=
  wf_numbering_intro
    (EQS: forall v rh,
          In (v, rh) n.(num_eqs) -> wf_equation n.(num_next) v rh)
    (REG: forall r v,
          PTree.get r n.(num_reg) = Some v -> Plt v n.(num_next))
    (VAL: forall r v,
          In r (PMap.get v n.(num_val)) -> PTree.get r n.(num_reg) = Some v).

Lemma wf_empty_numbering:
  wf_numbering empty_numbering.
Proof.
  unfold empty_numbering; split; simpl; intros.
  contradiction.
  rewrite PTree.gempty in H. congruence.
  rewrite PMap.gi in H. contradiction. 
Qed.

Lemma wf_rhs_increasing:
  forall next1 next2 rh,
  Ple next1 next2 ->
  wf_rhs next1 rh -> wf_rhs next2 rh.
Proof.
  intros; destruct rh; simpl; intros; apply Plt_Ple_trans with next1; auto.
Qed.

Lemma wf_equation_increasing:
  forall next1 next2 vr rh,
  Ple next1 next2 ->
  wf_equation next1 vr rh -> wf_equation next2 vr rh.
Proof.
  intros. destruct H0. split. 
  apply Plt_Ple_trans with next1; auto.
  apply wf_rhs_increasing with next1; auto.
Qed.

(** We now show that all operations over numberings 
  preserve well-formedness. *)

Lemma wf_valnum_reg:
  forall n r n' v,
  wf_numbering n ->
  valnum_reg n r = (n', v) ->
  wf_numbering n' /\ Plt v n'.(num_next) /\ Ple n.(num_next) n'.(num_next).
Proof.
  intros until v. unfold valnum_reg. intros WF VREG. inversion WF.
  destruct ((num_reg n)!r) as [v'|] eqn:?.
(* found *)
  inv VREG. split. auto. split. eauto. apply Ple_refl.
(* not found *)
  inv VREG. split. 
  split; simpl; intros.
  apply wf_equation_increasing with (num_next n). apply Ple_succ. auto. 
  rewrite PTree.gsspec in H. destruct (peq r0 r).
  inv H. apply Plt_succ.
  apply Plt_trans_succ; eauto.
  rewrite PMap.gsspec in H. destruct (peq v (num_next n)). 
  subst v. simpl in H. destruct H. subst r0. apply PTree.gss. contradiction.
  rewrite PTree.gso. eauto. exploit VAL; eauto. congruence. 
  simpl. split. apply Plt_succ. apply Ple_succ.
Qed.

Lemma wf_valnum_regs:
  forall rl n n' vl,
  wf_numbering n ->
  valnum_regs n rl = (n', vl) ->
  wf_numbering n' /\
  (forall v, In v vl -> Plt v n'.(num_next)) /\
  Ple n.(num_next) n'.(num_next).
Proof.
  induction rl; intros.
  simpl in H0. inversion H0. subst n'; subst vl. 
  simpl. intuition. 
  simpl in H0. 
  caseEq (valnum_reg n a). intros n1 v1 EQ1.
  caseEq (valnum_regs n1 rl). intros ns vs EQS.
  rewrite EQ1 in H0; rewrite EQS in H0; simpl in H0.
  inversion H0. subst n'; subst vl. 
  generalize (wf_valnum_reg _ _ _ _ H EQ1); intros [A1 [B1 C1]].
  generalize (IHrl _ _ _ A1 EQS); intros [As [Bs Cs]].
  split. auto.
  split. simpl; intros. elim H1; intro.
    subst v. eapply Plt_Ple_trans; eauto.
    auto.
  eapply Ple_trans; eauto.
Qed.

Lemma find_valnum_rhs_correct:
  forall rh vn eqs,
  find_valnum_rhs rh eqs = Some vn -> In (vn, rh) eqs.
Proof.
  induction eqs; simpl.
  congruence.
  case a; intros v r'. case (eq_rhs rh r'); intro.
  intro. left. congruence.
  intro. right. auto.
Qed.

Lemma find_valnum_num_correct:
  forall rh vn eqs,
  find_valnum_num vn eqs = Some rh -> In (vn, rh) eqs.
Proof.
  induction eqs; simpl.
  congruence.
  destruct a as [v' r']. destruct (peq vn v'); intros. 
  left. congruence.
  right. auto.
Qed.

Remark in_remove:
  forall (A: Type) (eq: forall (x y: A), {x=y}+{x<>y}) x y l,
  In y (List.remove eq x l) <-> x <> y /\ In y l.
Proof.
  induction l; simpl. 
  tauto.
  destruct (eq x a). 
  subst a. rewrite IHl. tauto. 
  simpl. rewrite IHl. intuition congruence.
Qed.

Lemma wf_forget_reg:
  forall n rd r v,
  wf_numbering n ->
  In r (PMap.get v (forget_reg n rd)) -> r <> rd /\ PTree.get r n.(num_reg) = Some v.
Proof.
  unfold forget_reg; intros. inversion H. 
  destruct ((num_reg n)!rd) as [vd|] eqn:?. 
  rewrite PMap.gsspec in H0. destruct (peq v vd). 
  subst vd. rewrite in_remove in H0. destruct H0. split. auto. eauto. 
  split; eauto. exploit VAL; eauto. congruence. 
  split; eauto. exploit VAL; eauto. congruence.
Qed.

Lemma wf_update_reg:
  forall n rd vd r v,
  wf_numbering n ->
  In r (PMap.get v (update_reg n rd vd)) -> PTree.get r (PTree.set rd vd n.(num_reg)) = Some v.
Proof.
  unfold update_reg; intros. inversion H. rewrite PMap.gsspec in H0. 
  destruct (peq v vd). 
  subst v; simpl in H0. destruct H0. 
  subst r. apply PTree.gss. 
  exploit wf_forget_reg; eauto. intros [A B]. rewrite PTree.gso; eauto. 
  exploit wf_forget_reg; eauto. intros [A B]. rewrite PTree.gso; eauto. 
Qed.

Lemma wf_add_rhs:
  forall n rd rh,
  wf_numbering n ->
  wf_rhs n.(num_next) rh ->
  wf_numbering (add_rhs n rd rh).
Proof.
  intros. inversion H. unfold add_rhs. 
  destruct (find_valnum_rhs rh n.(num_eqs)) as [vres|] eqn:?.
(* found *)
  exploit find_valnum_rhs_correct; eauto. intros IN. 
  split; simpl; intros. 
  auto.
  rewrite PTree.gsspec in H1. destruct (peq r rd). 
  inv H1. exploit EQS; eauto. intros [A B]. auto. 
  eauto. 
  eapply wf_update_reg; eauto. 
(* not found *)
  split; simpl; intros.
  destruct H1.
  inv H1. split. apply Plt_succ. apply wf_rhs_increasing with n.(num_next). apply Ple_succ. auto.
  apply wf_equation_increasing with n.(num_next). apply Ple_succ. auto.
  rewrite PTree.gsspec in H1. destruct (peq r rd). 
  inv H1. apply Plt_succ.
  apply Plt_trans_succ. eauto. 
  eapply wf_update_reg; eauto. 
Qed.

Lemma wf_add_op:
  forall n rd op rs,
  wf_numbering n ->
  wf_numbering (add_op n rd op rs).
Proof.
  intros. unfold add_op. destruct (is_move_operation op rs) as [r|] eqn:?.
(* move *)
  destruct (valnum_reg n r) as [n' v] eqn:?.
  exploit wf_valnum_reg; eauto. intros [A [B C]]. inversion A.
  constructor; simpl; intros.
  eauto.
  rewrite PTree.gsspec in H0. destruct (peq r0 rd). inv H0. auto. eauto.
  eapply wf_update_reg; eauto. 
(* not a move *)
  destruct (valnum_regs n rs) as [n' vs] eqn:?.
  exploit wf_valnum_regs; eauto. intros [A [B C]].
  eapply wf_add_rhs; eauto.
Qed.

Lemma wf_add_load:
  forall n rd chunk addr rs,
  wf_numbering n ->
  wf_numbering (add_load n rd chunk addr rs).
Proof.
  intros. unfold add_load. 
  caseEq (valnum_regs n rs). intros n' vl EQ. 
  generalize (wf_valnum_regs _ _ _ _ H EQ). intros [A [B C]].
  apply wf_add_rhs; auto.
Qed.

Lemma wf_add_unknown:
  forall n rd,
  wf_numbering n ->
  wf_numbering (add_unknown n rd).
Proof.
  intros. inversion H. unfold add_unknown. constructor; simpl; intros.
  eapply wf_equation_increasing; eauto. auto with coqlib. 
  rewrite PTree.gsspec in H0. destruct (peq r rd). 
  inv H0. auto with coqlib.
  apply Plt_trans_succ; eauto.
  exploit wf_forget_reg; eauto. intros [A B]. rewrite PTree.gso; eauto.
Qed.

Remark kill_eqs_in:
  forall pred v rhs eqs,
  In (v, rhs) (kill_eqs pred eqs) -> In (v, rhs) eqs /\ pred rhs = false.
Proof.
  induction eqs; simpl; intros. 
  tauto.
  destruct (pred (snd a)) eqn:?. 
  exploit IHeqs; eauto. tauto. 
  simpl in H; destruct H. subst a. auto. exploit IHeqs; eauto. tauto. 
Qed.

Lemma wf_kill_equations:
  forall pred n, wf_numbering n -> wf_numbering (kill_equations pred n).
Proof.
  intros. inversion H. unfold kill_equations; split; simpl; intros.
  exploit kill_eqs_in; eauto. intros [A B]. auto. 
  eauto.
  eauto.
Qed.

Lemma wf_add_store:
  forall n chunk addr rargs rsrc,
  wf_numbering n -> wf_numbering (add_store n chunk addr rargs rsrc).
Proof.
  intros. unfold add_store. 
  destruct (valnum_regs n rargs) as [n1 vargs] eqn:?.
  exploit wf_valnum_regs; eauto. intros [A [B C]].
  assert (wf_numbering (kill_equations (filter_after_store chunk addr vargs) n1)).
    apply wf_kill_equations. auto.
  destruct chunk; auto; apply wf_add_rhs; auto.
Qed.

Lemma wf_transfer:
  forall f pc n, wf_numbering n -> wf_numbering (transfer f pc n).
Proof.
  intros. unfold transfer. 
  destruct (f.(fn_code)!pc); auto.
  destruct i; auto.
  apply wf_add_op; auto.
  apply wf_add_load; auto.
  apply wf_add_store; auto.
  apply wf_empty_numbering.
  apply wf_empty_numbering.
  apply wf_add_unknown. apply wf_kill_equations; auto.
Qed.

(** As a consequence, the numberings computed by the static analysis
  are well formed. *)

Theorem wf_analyze:
  forall f approx pc, analyze f = Some approx -> wf_numbering approx!!pc.
Proof.
  unfold analyze; intros.
  eapply Solver.fixpoint_invariant with (P := wf_numbering); eauto.
  exact wf_empty_numbering.   
  exact (wf_transfer f).
Qed.

(** ** Properties of satisfiability of numberings *)

Module ValnumEq.
  Definition t := valnum.
  Definition eq := peq.
End ValnumEq.

Module VMap := EMap(ValnumEq).

Section SATISFIABILITY.

Variable ge: genv.
Variable sp: val.

(** Agremment between two mappings from value numbers to values
  up to a given value number. *)

Definition valu_agree (valu1 valu2: valnum -> val) (upto: valnum) : Prop :=
  forall v, Plt v upto -> valu2 v = valu1 v.

Lemma valu_agree_refl:
  forall valu upto, valu_agree valu valu upto.
Proof.
  intros; red; auto.
Qed.

Lemma valu_agree_trans:
  forall valu1 valu2 valu3 upto12 upto23,
  valu_agree valu1 valu2 upto12 ->
  valu_agree valu2 valu3 upto23 ->
  Ple upto12 upto23 ->
  valu_agree valu1 valu3 upto12.
Proof.
  intros; red; intros. transitivity (valu2 v).
  apply H0. apply Plt_Ple_trans with upto12; auto.
  apply H; auto.
Qed.

Lemma valu_agree_list:
  forall valu1 valu2 upto vl,
  valu_agree valu1 valu2 upto ->
  (forall v, In v vl -> Plt v upto) ->
  map valu2 vl = map valu1 vl.
Proof.
  intros. apply list_map_exten. intros. symmetry. apply H. auto.
Qed.

(** The [numbering_holds] predicate (defined in file [CSE]) is
  extensional with respect to [valu_agree]. *)

Lemma numbering_holds_exten:
  forall valu1 valu2 n rs m,
  valu_agree valu1 valu2 n.(num_next) ->
  wf_numbering n ->
  numbering_holds valu1 ge sp rs m n ->
  numbering_holds valu2 ge sp rs m n.
Proof.
  intros. inversion H0. inversion H1. split; intros.
  exploit EQS; eauto. intros [A B]. red in B.
  generalize (H2 _ _ H4).
  unfold equation_holds; destruct rh.
  rewrite (valu_agree_list valu1 valu2 n.(num_next)). 
  rewrite H. auto. auto. auto. auto.
  rewrite (valu_agree_list valu1 valu2 n.(num_next)). 
  rewrite H. auto. auto. auto. auto. 
  rewrite H. auto. eauto.
Qed.

(** [valnum_reg] and [valnum_regs] preserve the [numbering_holds] predicate.
  Moreover, it is always the case that the returned value number has
  the value of the given register in the final assignment of values to
  value numbers. *)

Lemma valnum_reg_holds:
  forall valu1 rs n r n' v m,
  wf_numbering n ->
  numbering_holds valu1 ge sp rs m n ->
  valnum_reg n r = (n', v) ->
  exists valu2,
    numbering_holds valu2 ge sp rs m n' /\
    valu2 v = rs#r /\
    valu_agree valu1 valu2 n.(num_next).
Proof.
  intros until v. unfold valnum_reg. 
  caseEq (n.(num_reg)!r).
  (* Register already has a value number *)
  intros. inversion H2. subst n'; subst v0. 
  inversion H1. 
  exists valu1. split. auto. 
  split. symmetry. auto.
  apply valu_agree_refl.
  (* Register gets a fresh value number *)
  intros. inversion H2. subst n'. subst v. inversion H1.
  set (valu2 := VMap.set n.(num_next) rs#r valu1).
  assert (AG: valu_agree valu1 valu2 n.(num_next)).
    red; intros. unfold valu2. apply VMap.gso. 
    auto with coqlib.
  destruct (numbering_holds_exten _ _ _ _ _ AG H0 H1) as [A B].
  exists valu2. 
  split. split; simpl; intros. auto. 
  unfold valu2, VMap.set, ValnumEq.eq. 
  rewrite PTree.gsspec in H5. destruct (peq r0 r).
  inv H5. rewrite peq_true. auto.
  rewrite peq_false. auto. 
  assert (Plt vn (num_next n)). inv H0. eauto. 
  red; intros; subst; eapply Plt_strict; eauto. 
  split. unfold valu2. rewrite VMap.gss. auto. 
  auto.
Qed.

Lemma valnum_regs_holds:
  forall rs rl valu1 n n' vl m,
  wf_numbering n ->
  numbering_holds valu1 ge sp rs m n ->
  valnum_regs n rl = (n', vl) ->
  exists valu2,
    numbering_holds valu2 ge sp rs m n' /\
    List.map valu2 vl = rs##rl /\
    valu_agree valu1 valu2 n.(num_next).
Proof.
  induction rl; simpl; intros.
  (* base case *)
  inversion H1; subst n'; subst vl.
  exists valu1. split. auto. split. auto. apply valu_agree_refl.
  (* inductive case *)
  caseEq (valnum_reg n a); intros n1 v1 EQ1.
  caseEq (valnum_regs n1 rl); intros ns vs EQs.
  rewrite EQ1 in H1; rewrite EQs in H1. inversion H1. subst vl; subst n'.
  generalize (valnum_reg_holds _ _ _ _ _ _ _ H H0 EQ1).
  intros [valu2 [A [B C]]].
  generalize (wf_valnum_reg _ _ _ _ H EQ1). intros [D [E F]].
  generalize (IHrl _ _ _ _ _ D A EQs). 
  intros [valu3 [P [Q R]]].
  exists valu3. 
  split. auto. 
  split. simpl. rewrite R. congruence. auto.
  eapply valu_agree_trans; eauto.
Qed.

(** A reformulation of the [equation_holds] predicate in terms
  of the value to which a right-hand side of an equation evaluates. *)

Definition rhs_evals_to
    (valu: valnum -> val) (rh: rhs) (m: mem) (v: val) : Prop :=
  match rh with
  | Op op vl => 
      eval_operation ge sp op (List.map valu vl) m = Some v
  | Load chunk addr vl =>
      exists a,
      eval_addressing ge sp addr (List.map valu vl) = Some a /\
      Mem.loadv chunk m a = Some v
  end.

Lemma equation_evals_to_holds_1:
  forall valu rh v vres m,
  rhs_evals_to valu rh m v ->
  equation_holds valu ge sp m vres rh ->
  valu vres = v.
Proof.
  intros until m. unfold rhs_evals_to, equation_holds.
  destruct rh. congruence.
  intros [a1 [A1 B1]] [a2 [A2 B2]]. congruence.
Qed.

Lemma equation_evals_to_holds_2:
  forall valu rh v vres m,
  wf_rhs vres rh ->
  rhs_evals_to valu rh m v ->
  equation_holds (VMap.set vres v valu) ge sp m vres rh.
Proof.
  intros until m. unfold wf_rhs, rhs_evals_to, equation_holds.
  rewrite VMap.gss. 
  assert (forall vl: list valnum,
            (forall v, In v vl -> Plt v vres) ->
            map (VMap.set vres v valu) vl = map valu vl).
    intros. apply list_map_exten. intros. 
    symmetry. apply VMap.gso. apply Plt_ne. auto.
  destruct rh; intros; rewrite H; auto.
Qed.

(** The numbering obtained by adding an equation [rd = rhs] is satisfiable
  in a concrete register set where [rd] is set to the value of [rhs]. *)

Lemma add_rhs_satisfiable_gen:
  forall n rh valu1 rs rd rs' m,
  wf_numbering n ->
  wf_rhs n.(num_next) rh ->
  numbering_holds valu1 ge sp rs m n ->
  rhs_evals_to valu1 rh m (rs'#rd) ->
  (forall r, r <> rd -> rs'#r = rs#r) ->
  numbering_satisfiable ge sp rs' m (add_rhs n rd rh).
Proof.
  intros. unfold add_rhs. 
  caseEq (find_valnum_rhs rh n.(num_eqs)).
  (* RHS found *)
  intros vres FINDVN. inversion H1.
  exists valu1. split; simpl; intros.
  auto. 
  rewrite PTree.gsspec in H6.
  destruct (peq r rd).
  inv H6. 
  symmetry. eapply equation_evals_to_holds_1; eauto.
  apply H4. apply find_valnum_rhs_correct. congruence.
  rewrite H3; auto.
  (* RHS not found *)
  intro FINDVN. 
  set (valu2 := VMap.set n.(num_next) (rs'#rd) valu1).
  assert (AG: valu_agree valu1 valu2 n.(num_next)).
    red; intros. unfold valu2. apply VMap.gso. 
    auto with coqlib.
  elim (numbering_holds_exten _ _ _ _ _ AG H H1); intros.
  exists valu2. split; simpl; intros.
  destruct H6. 
  inv H6. unfold valu2. eapply equation_evals_to_holds_2; eauto. auto. 
  rewrite PTree.gsspec in H6. destruct (peq r rd).
  unfold valu2. inv H6. rewrite VMap.gss. auto.
  rewrite H3; auto.
Qed.

Lemma add_rhs_satisfiable:
  forall n rh valu1 rs rd v m,
  wf_numbering n ->
  wf_rhs n.(num_next) rh ->
  numbering_holds valu1 ge sp rs m n ->
  rhs_evals_to valu1 rh m v ->
  numbering_satisfiable ge sp (rs#rd <- v) m (add_rhs n rd rh).
Proof.
  intros. eapply add_rhs_satisfiable_gen; eauto. 
  rewrite Regmap.gss; auto.
  intros. apply Regmap.gso; auto.
Qed.

(** [add_op] returns a numbering that is satisfiable in the register
  set after execution of the corresponding [Iop] instruction. *)

Lemma add_op_satisfiable:
  forall n rs op args dst v m,
  wf_numbering n ->
  numbering_satisfiable ge sp rs m n ->
  eval_operation ge sp op rs##args m = Some v ->
  numbering_satisfiable ge sp (rs#dst <- v) m (add_op n dst op args).
Proof.
  intros. inversion H0.
  unfold add_op.
  caseEq (@is_move_operation reg op args).
  intros arg EQ. 
  destruct (is_move_operation_correct _ _ EQ) as [A B]. subst op args.
  caseEq (valnum_reg n arg). intros n1 v1 VL.
  generalize (valnum_reg_holds _ _ _ _ _ _ _ H H2 VL). intros [valu2 [A [B C]]].
  generalize (wf_valnum_reg _ _ _ _ H VL). intros [D [E F]].  
  elim A; intros. exists valu2; split; simpl; intros.
  auto. rewrite Regmap.gsspec. rewrite PTree.gsspec in H5.
  destruct (peq r dst). simpl in H1. congruence. auto.
  intro NEQ. caseEq (valnum_regs n args). intros n1 vl VRL.
  generalize (valnum_regs_holds _ _ _ _ _ _ _ H H2 VRL). intros [valu2 [A [B C]]].
  generalize (wf_valnum_regs _ _ _ _ H VRL). intros [D [E F]].
  apply add_rhs_satisfiable with valu2; auto.
  simpl. congruence. 
Qed.

(** [add_load] returns a numbering that is satisfiable in the register
  set after execution of the corresponding [Iload] instruction. *)

Lemma add_load_satisfiable:
  forall n rs chunk addr args dst a v m,
  wf_numbering n ->
  numbering_satisfiable ge sp rs m n ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.loadv chunk m a = Some v ->
  numbering_satisfiable ge sp (rs#dst <- v) m (add_load n dst chunk addr args).
Proof.
  intros. inversion H0.
  unfold add_load.
  caseEq (valnum_regs n args). intros n1 vl VRL.
  generalize (valnum_regs_holds _ _ _ _ _ _ _ H H3 VRL). intros [valu2 [A [B C]]].
  generalize (wf_valnum_regs _ _ _ _ H VRL). intros [D [E F]].
  apply add_rhs_satisfiable with valu2; auto.
  simpl. exists a; split; congruence. 
Qed.

(** [add_unknown] returns a numbering that is satisfiable in the
  register set after setting the target register to any value. *)

Lemma add_unknown_satisfiable:
  forall n rs dst v m,
  wf_numbering n ->
  numbering_satisfiable ge sp rs m n ->
  numbering_satisfiable ge sp (rs#dst <- v) m (add_unknown n dst).
Proof.
  intros. destruct H0 as [valu A]. 
  set (valu' := VMap.set n.(num_next) v valu).
  assert (numbering_holds valu' ge sp rs m n). 
    eapply numbering_holds_exten; eauto.
    unfold valu'; red; intros. apply VMap.gso. auto with coqlib.
  destruct H0 as [B C].
  exists valu'; split; simpl; intros.
  eauto.
  rewrite PTree.gsspec in H0. rewrite Regmap.gsspec. 
  destruct (peq r dst). inversion H0. unfold valu'. rewrite VMap.gss; auto.
  eauto.
Qed.

(** Satisfiability of [kill_equations]. *)

Lemma kill_equations_holds:
  forall pred valu n rs m m',
  (forall v r,
   equation_holds valu ge sp m v r -> pred r = false -> equation_holds valu ge sp m' v r) ->
  numbering_holds valu ge sp rs m n ->
  numbering_holds valu ge sp rs m' (kill_equations pred n).
Proof.
  intros. destruct H0 as [A B]. red; simpl. split; intros. 
  exploit kill_eqs_in; eauto. intros [C D]. eauto. 
  auto.
Qed.

(** [kill_loads] preserves satisfiability.  Moreover, the resulting numbering
  is satisfiable in any concrete memory state. *)

Lemma kill_loads_satisfiable:
  forall n rs m m',
  numbering_satisfiable ge sp rs m n ->
  numbering_satisfiable ge sp rs m' (kill_loads n).
Proof.
  intros. destruct H as [valu A]. exists valu. eapply kill_equations_holds with (m := m); eauto.
  intros. destruct r; simpl in *. rewrite <- H. apply op_depends_on_memory_correct; auto. 
  congruence.
Qed.

(** [add_store] returns a numbering that is satisfiable in the memory state
  after execution of the corresponding [Istore] instruction. *)

Lemma add_store_satisfiable:
  forall n rs chunk addr args src a m m',
  wf_numbering n ->
  numbering_satisfiable ge sp rs m n ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.storev chunk m a (rs#src) = Some m' ->
  Val.has_type (rs#src) (type_of_chunk chunk) ->
  numbering_satisfiable ge sp rs m' (add_store n chunk addr args src).
Proof.
  intros. unfold add_store. destruct H0 as [valu A].
  destruct (valnum_regs n args) as [n1 vargs] eqn:?.
  exploit valnum_regs_holds; eauto. intros [valu' [B [C D]]].
  exploit wf_valnum_regs; eauto. intros [U [V W]].
  set (n2 := kill_equations (filter_after_store chunk addr vargs) n1).
  assert (numbering_holds valu' ge sp rs m' n2).
    apply kill_equations_holds with (m := m); auto.
    intros. destruct r; simpl in *. 
    rewrite <- H0. apply op_depends_on_memory_correct; auto.
    destruct H0 as [a' [P Q]]. 
    destruct (eq_list_valnum vargs l); simpl in H4; try congruence. subst l.
    rewrite negb_false_iff in H4.
    exists a'; split; auto. 
    destruct a; simpl in H2; try congruence.
    destruct a'; simpl in Q; try congruence.
    simpl. rewrite <- Q. 
    rewrite C in P. eapply Mem.load_store_other; eauto.
    exploit addressing_separated_sound; eauto. intuition congruence.
  assert (N2: numbering_satisfiable ge sp rs m' n2).
    exists valu'; auto.
  set (n3 := add_rhs n2 src (Load chunk addr vargs)).
  assert (N3: Val.load_result chunk (rs#src) = rs#src -> numbering_satisfiable ge sp rs m' n3).
    intro EQ. unfold n3. apply add_rhs_satisfiable_gen with valu' rs.
    apply wf_kill_equations; auto.
    red. auto. auto.
    red. exists a; split. congruence. 
    rewrite <- EQ. destruct a; simpl in H2; try discriminate. simpl. 
    eapply Mem.load_store_same; eauto. 
    auto.
  destruct chunk; auto; apply N3. 
  simpl in H3. destruct (rs#src); auto || contradiction.
  simpl in H3. destruct (rs#src); auto || contradiction.
Qed.

(** Correctness of [reg_valnum]: if it returns a register [r],
  that register correctly maps back to the given value number. *)

Lemma reg_valnum_correct:
  forall n v r, wf_numbering n -> reg_valnum n v = Some r -> n.(num_reg)!r = Some v.
Proof.
  unfold reg_valnum; intros. inv H. 
  destruct ((num_val n)#v) as [| r1 rl] eqn:?; inv H0. 
  eapply VAL. rewrite Heql. auto with coqlib.
Qed.

(** Correctness of [find_rhs]: if successful and in a
  satisfiable numbering, the returned register does contain the 
  result value of the operation or memory load. *)

Lemma find_rhs_correct:
  forall valu rs m n rh r,
  wf_numbering n ->
  numbering_holds valu ge sp rs m n ->
  find_rhs n rh = Some r ->
  rhs_evals_to valu rh m rs#r.
Proof.
  intros until r. intros WF NH. 
  unfold find_rhs. 
  caseEq (find_valnum_rhs rh n.(num_eqs)); intros.
  exploit find_valnum_rhs_correct; eauto. intros.
  exploit reg_valnum_correct; eauto. intros.
  inversion NH. 
  generalize (H3 _ _ H1). rewrite (H4 _ _ H2). 
  destruct rh; simpl; auto.
  discriminate.
Qed.

(** Correctness of operator reduction *)

Section REDUCE.

Variable A: Type.
Variable f: (valnum -> option rhs) -> A -> list valnum -> option (A * list valnum).
Variable V: Type.
Variable rs: regset.
Variable m: mem.
Variable sem: A -> list val -> option V.
Hypothesis f_sound:
  forall eqs valu op args op' args',
  (forall v rhs, eqs v = Some rhs -> equation_holds valu ge sp m v rhs) ->
  f eqs op args = Some(op', args') ->
  sem op' (map valu args') = sem op (map valu args).
Variable n: numbering.
Variable valu: valnum -> val.
Hypothesis n_holds: numbering_holds valu ge sp rs m n.
Hypothesis n_wf: wf_numbering n.

Lemma regs_valnums_correct:
  forall vl rl, regs_valnums n vl = Some rl -> rs##rl = map valu vl.
Proof.
  induction vl; simpl; intros.
  inv H. auto.
  destruct (reg_valnum n a) as [r1|] eqn:?; try discriminate.
  destruct (regs_valnums n vl) as [rx|] eqn:?; try discriminate.
  inv H. simpl; decEq; auto. 
  eapply (proj2 n_holds); eauto. eapply reg_valnum_correct; eauto.
Qed.

Lemma reduce_rec_sound:
  forall niter op args op' rl' res,
  reduce_rec A f n niter op args = Some(op', rl') ->
  sem op (map valu args) = Some res ->
  sem op' (rs##rl') = Some res.
Proof.
  induction niter; simpl; intros.
  discriminate.
  destruct (f (fun v : valnum => find_valnum_num v (num_eqs n)) op args)
           as [[op1 args1] | ] eqn:?.
  assert (sem op1 (map valu args1) = Some res).
    rewrite <- H0. eapply f_sound; eauto.
    simpl; intros. apply (proj1 n_holds). eapply find_valnum_num_correct; eauto. 
  destruct (reduce_rec A f n niter op1 args1) as [[op2 rl2] | ] eqn:?.
  inv H. eapply IHniter; eauto.
  destruct (regs_valnums n args1) as [rl|] eqn:?.
  inv H. erewrite regs_valnums_correct; eauto.
  discriminate.
  discriminate.
Qed.

Lemma reduce_sound:
  forall op rl vl op' rl' res,
  reduce A f n op rl vl = (op', rl') ->
  map valu vl = rs##rl ->
  sem op rs##rl = Some res ->
  sem op' rs##rl' = Some res.
Proof.
  unfold reduce; intros. 
  destruct (reduce_rec A f n 4%nat op vl) as [[op1 rl1] | ] eqn:?; inv H.
  eapply reduce_rec_sound; eauto. congruence.
  auto.
Qed.

End REDUCE.

End SATISFIABILITY.

(** The numberings associated to each instruction by the static analysis
  are inductively satisfiable, in the following sense: the numbering
  at the function entry point is satisfiable, and for any RTL execution 
  from [pc] to [pc'], satisfiability at [pc] implies 
  satisfiability at [pc']. *)

Theorem analysis_correct_1:
  forall ge sp rs m f approx pc pc' i,
  analyze f = Some approx ->
  f.(fn_code)!pc = Some i -> In pc' (successors_instr i) ->
  numbering_satisfiable ge sp rs m (transfer f pc approx!!pc) ->
  numbering_satisfiable ge sp rs m approx!!pc'.
Proof.
  intros.
  assert (Numbering.ge approx!!pc' (transfer f pc approx!!pc)).
    eapply Solver.fixpoint_solution; eauto.
    unfold successors_list, successors. rewrite PTree.gmap1.
    rewrite H0. auto.
  apply H3. auto.
Qed.

Theorem analysis_correct_entry:
  forall ge sp rs m f approx,
  analyze f = Some approx ->
  numbering_satisfiable ge sp rs m approx!!(f.(fn_entrypoint)).
Proof.
  intros. 
  replace (approx!!(f.(fn_entrypoint))) with Solver.L.top.
  apply empty_numbering_satisfiable.
  symmetry. eapply Solver.fixpoint_entry; eauto.
Qed.

(** * Semantic preservation *)

Section PRESERVATION.

Variable prog: program.
Variable tprog : program.
Hypothesis TRANSF: transf_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf_partial transf_fundef prog TRANSF).

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof (Genv.find_var_info_transf_partial transf_fundef prog TRANSF).

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial transf_fundef prog TRANSF).

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial transf_fundef prog TRANSF).

Lemma sig_preserved:
  forall f tf, transf_fundef f = OK tf -> funsig tf = funsig f.
Proof.
  unfold transf_fundef; intros. destruct f; monadInv H; auto.
  unfold transf_function in EQ. destruct (type_function f); try discriminate. 
  destruct (analyze f); try discriminate. inv EQ; auto. 
Qed.

Lemma find_function_translated:
  forall ros rs f,
  find_function ge ros rs = Some f ->
  exists tf, find_function tge ros rs = Some tf /\ transf_fundef f = OK tf.
Proof.
  intros until f; destruct ros; simpl.
  intro. apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); intro.
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

Definition transf_function' (f: function) (approxs: PMap.t numbering) : function :=
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (transf_code approxs f.(fn_code))
    f.(fn_entrypoint).

(** The proof of semantic preservation is a simulation argument using
  diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                   |t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  Left: RTL execution in the original program.  Right: RTL execution in
  the optimized program.  Precondition (top) and postcondition (bottom):
  agreement between the states, including the fact that
  the numbering at [pc] (returned by the static analysis) is satisfiable.
*)

Inductive match_stackframes: list stackframe -> list stackframe -> typ -> Prop :=
  | match_stackframes_nil:
      match_stackframes nil nil Tint
  | match_stackframes_cons:
      forall res sp pc rs f approx tyenv s s' ty
           (ANALYZE: analyze f = Some approx)
           (WTF: wt_function f tyenv)
           (WTREGS: wt_regset tyenv rs)
           (TYRES: tyenv res = ty)
           (SAT: forall v m, numbering_satisfiable ge sp (rs#res <- v) m approx!!pc)
           (STACKS: match_stackframes s s' (proj_sig_res (fn_sig f))),
    match_stackframes
      (Stackframe res f sp pc rs :: s)
      (Stackframe res (transf_function' f approx) sp pc rs :: s')
      ty.

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m s' f approx tyenv
             (ANALYZE: analyze f = Some approx)
             (WTF: wt_function f tyenv)
             (WTREGS: wt_regset tyenv rs)
             (SAT: numbering_satisfiable ge sp rs m approx!!pc)
             (STACKS: match_stackframes s s' (proj_sig_res (fn_sig f))),
      match_states (State s f sp pc rs m)
                   (State s' (transf_function' f approx) sp pc rs m)
  | match_states_call:
      forall s f tf args m s',
      match_stackframes s s' (proj_sig_res (funsig f)) ->
      Val.has_type_list args (sig_args (funsig f)) ->
      transf_fundef f = OK tf ->
      match_states (Callstate s f args m)
                   (Callstate s' tf args m)
  | match_states_return:
      forall s s' ty v m,
      match_stackframes s s' ty ->
      Val.has_type v ty ->
      match_states (Returnstate s v m)
                   (Returnstate s' v m).

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc ?c = Some ?instr), f: function, approx: PMap.t numbering |- _ =>
      cut ((transf_function' f approx).(fn_code)!pc = Some(transf_instr approx!!pc instr));
      [ simpl transf_instr
      | unfold transf_function', transf_code; simpl; rewrite PTree.gmap; 
        unfold option_map; rewrite H1; reflexivity ]
  end.

(** The proof of simulation is a case analysis over the transition
  in the source code. *)

Lemma transf_step_correct:
  forall s1 t s2, step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; inv MS; try (TransfInstr; intro C).

  (* Inop *)
  exists (State s' (transf_function' f approx) sp pc' rs m); split.
  apply exec_Inop; auto.
  econstructor; eauto. 
  eapply analysis_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H; auto.

  (* Iop *)
  exists (State s' (transf_function' f approx) sp pc' (rs#res <- v) m); split.
  destruct (is_trivial_op op) eqn:?.
  eapply exec_Iop'; eauto.
  rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  assert (wf_numbering approx!!pc). eapply wf_analyze; eauto.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros [valu2 [NH2 [EQ AG]]]. 
  assert (wf_numbering n1). eapply wf_valnum_regs; eauto. 
  destruct (find_rhs n1 (Op op vl)) as [r|] eqn:?.
  (* replaced by move *)
  assert (EV: rhs_evals_to ge sp valu2 (Op op vl) m rs#r). eapply find_rhs_correct; eauto.
  assert (RES: rs#r = v). red in EV. congruence.
  eapply exec_Iop'; eauto. simpl. congruence. 
  (* possibly simplified *)
  destruct (reduce operation combine_op n1 op args vl) as [op' args'] eqn:?.
  assert (RES: eval_operation ge sp op' rs##args' m = Some v).
    eapply reduce_sound with (sem := fun op vl => eval_operation ge sp op vl m); eauto. 
    intros; eapply combine_op_sound; eauto.
  eapply exec_Iop'; eauto.
  rewrite <- RES. apply eval_operation_preserved. exact symbols_preserved.
  (* state matching *)
  econstructor; eauto.
  apply wt_regset_assign; auto. 
  generalize (wt_instrs _ _ WTF pc _ H); intro WTI; inv WTI.
  simpl in H0. inv H0. rewrite <- H3. apply WTREGS.
  replace (tyenv res) with (snd (type_of_operation op)).
  eapply type_of_operation_sound; eauto.
  rewrite <- H6. reflexivity.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H. 
  eapply add_op_satisfiable; eauto. eapply wf_analyze; eauto.

  (* Iload *)
  exists (State s' (transf_function' f approx) sp pc' (rs#dst <- v) m); split.
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  assert (wf_numbering approx!!pc). eapply wf_analyze; eauto.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros [valu2 [NH2 [EQ AG]]]. 
  assert (wf_numbering n1). eapply wf_valnum_regs; eauto. 
  destruct (find_rhs n1 (Load chunk addr vl)) as [r|] eqn:?.
  (* replaced by move *)
  assert (EV: rhs_evals_to ge sp valu2 (Load chunk addr vl) m rs#r). eapply find_rhs_correct; eauto.
  assert (RES: rs#r = v). red in EV. destruct EV as [a' [EQ1 EQ2]]. congruence.
  eapply exec_Iop'; eauto. simpl. congruence. 
  (* possibly simplified *)
  destruct (reduce addressing combine_addr n1 addr args vl) as [addr' args'] eqn:?.
  assert (ADDR: eval_addressing ge sp addr' rs##args' = Some a).
    eapply reduce_sound with (sem := fun addr vl => eval_addressing ge sp addr vl); eauto. 
    intros; eapply combine_addr_sound; eauto.
  assert (ADDR': eval_addressing tge sp addr' rs##args' = Some a).
    rewrite <- ADDR. apply eval_addressing_preserved. exact symbols_preserved.
  eapply exec_Iload; eauto.
  (* state matching *)
  econstructor; eauto.
  generalize (wt_instrs _ _ WTF pc _ H); intro WTI; inv WTI.
  apply wt_regset_assign. auto. rewrite H8. eapply type_of_chunk_correct; eauto.
  eapply analysis_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. 
  eapply add_load_satisfiable; eauto. eapply wf_analyze; eauto.

  (* Istore *)
  exists (State s' (transf_function' f approx) sp pc' rs m'); split.
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  assert (wf_numbering approx!!pc). eapply wf_analyze; eauto.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros [valu2 [NH2 [EQ AG]]]. 
  assert (wf_numbering n1). eapply wf_valnum_regs; eauto. 
  destruct (reduce addressing combine_addr n1 addr args vl) as [addr' args'] eqn:?.
  assert (ADDR: eval_addressing ge sp addr' rs##args' = Some a).
    eapply reduce_sound with (sem := fun addr vl => eval_addressing ge sp addr vl); eauto. 
    intros; eapply combine_addr_sound; eauto.
  assert (ADDR': eval_addressing tge sp addr' rs##args' = Some a).
    rewrite <- ADDR. apply eval_addressing_preserved. exact symbols_preserved.
  eapply exec_Istore; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H.
  eapply add_store_satisfiable; eauto. eapply wf_analyze; eauto.
  generalize (wt_instrs _ _ WTF pc _ H); intro WTI; inv WTI.
  rewrite <- H8. auto.

  (* Icall *)
  exploit find_function_translated; eauto. intros [tf [FIND' TRANSF']]. 
  econstructor; split.
  eapply exec_Icall; eauto.
  apply sig_preserved; auto.
  generalize (wt_instrs _ _ WTF pc _ H); intro WTI; inv WTI.
  econstructor; eauto. 
  econstructor; eauto. 
  intros. eapply analysis_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. 
  apply empty_numbering_satisfiable.
  rewrite <- H7. apply wt_regset_list; auto. 

  (* Itailcall *)
  exploit find_function_translated; eauto. intros [tf [FIND' TRANSF']]. 
  econstructor; split.
  eapply exec_Itailcall; eauto.
  apply sig_preserved; auto.
  generalize (wt_instrs _ _ WTF pc _ H); intro WTI; inv WTI.
  econstructor; eauto. 
  replace (proj_sig_res (funsig fd)) with (proj_sig_res (fn_sig f)). auto. 
  unfold proj_sig_res. rewrite H6; auto.
  rewrite <- H7. apply wt_regset_list; auto.

  (* Ibuiltin *)
  econstructor; split.
  eapply exec_Ibuiltin; eauto. 
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  generalize (wt_instrs _ _ WTF pc _ H); intro WTI; inv WTI.
  econstructor; eauto.
  apply wt_regset_assign; auto. 
  rewrite H6. eapply external_call_well_typed; eauto. 
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H. 
  apply add_unknown_satisfiable. apply wf_kill_equations. eapply wf_analyze; eauto.
  eapply kill_loads_satisfiable; eauto. 

  (* Icond *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  assert (wf_numbering approx!!pc). eapply wf_analyze; eauto.
  elim SAT; intros valu1 NH1.
  exploit valnum_regs_holds; eauto. intros [valu2 [NH2 [EQ AG]]]. 
  assert (wf_numbering n1). eapply wf_valnum_regs; eauto. 
  destruct (reduce condition combine_cond n1 cond args vl) as [cond' args'] eqn:?.
  assert (RES: eval_condition cond' rs##args' m = Some b).
    eapply reduce_sound with (sem := fun cond vl => eval_condition cond vl m); eauto. 
    intros; eapply combine_cond_sound; eauto.
  econstructor; split.
  eapply exec_Icond; eauto. 
  econstructor; eauto.
  destruct b; eapply analysis_correct_1; eauto; simpl; auto;
  unfold transfer; rewrite H; auto.

  (* Ijumptable *)
  econstructor; split.
  eapply exec_Ijumptable; eauto. 
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl. eapply list_nth_z_in; eauto.
  unfold transfer; rewrite H; auto.

  (* Ireturn *)
  econstructor; split.
  eapply exec_Ireturn; eauto.
  econstructor; eauto.
  generalize (wt_instrs _ _ WTF pc _ H); intro WTI; inv WTI.
  unfold proj_sig_res. rewrite <- H2. destruct or; simpl; auto. 

  (* internal function *)
  monadInv H7. unfold transf_function in EQ. 
  destruct (type_function f) as [tyenv|] eqn:?; try discriminate.
  destruct (analyze f) as [approx|] eqn:?; inv EQ. 
  assert (WTF: wt_function f tyenv). apply type_function_correct; auto.
  econstructor; split.
  eapply exec_function_internal; eauto. 
  simpl. econstructor; eauto.
  apply wt_init_regs. inv WTF. rewrite wt_params; auto.
  apply analysis_correct_entry; auto.

  (* external function *)
  monadInv H7. 
  econstructor; split.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.
  simpl. eapply external_call_well_typed; eauto. 

  (* return *)
  inv H3.
  econstructor; split.
  eapply exec_return; eauto.
  econstructor; eauto.
  apply wt_regset_assign; auto. 
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. 
  exploit funct_ptr_translated; eauto. intros [tf [A B]].
  exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
  eapply Genv.init_mem_transf_partial; eauto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry. eapply transform_partial_program_main; eauto.
  rewrite <- H3. apply sig_preserved; auto.
  constructor. rewrite H3. constructor. rewrite H3. constructor. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H4. constructor. 
Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_step.
  eexact symbols_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transf_step_correct. 
Qed.

End PRESERVATION.

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

Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL.
Require Import ValueDomain ValueAOp ValueAnalysis.
Require Import CSEdomain CombineOp CombineOpproof CSE.

Definition match_prog (prog tprog: RTL.program) :=
  match_program (fun cu f tf => transf_fundef (romem_for cu) f = OK tf) eq prog tprog.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

(** * Soundness of operations over value numberings *)

Remark wf_equation_incr:
  forall next1 next2 e,
  wf_equation next1 e -> Ple next1 next2 -> wf_equation next2 e.
Proof.
  unfold wf_equation; intros; destruct e. destruct H. split.
  apply Pos.lt_le_trans with next1; auto.
  red; intros. apply Pos.lt_le_trans with next1; auto. apply H1; auto.
Qed.

(** Extensionality with respect to valuations. *)

Definition valu_agree (valu1 valu2: valuation) (upto: valnum) :=
  forall v, Plt v upto -> valu2 v = valu1 v.

Section EXTEN.

Variable valu1: valuation.
Variable upto: valnum.
Variable valu2: valuation.
Hypothesis AGREE: valu_agree valu1 valu2 upto.
Variable ge: genv.
Variable sp: val.
Variable rs: regset.
Variable m: mem.

Lemma valnums_val_exten:
  forall vl,
  (forall v, In v vl -> Plt v upto) ->
  map valu2 vl = map valu1 vl.
Proof.
  intros. apply list_map_exten. intros. symmetry. auto.
Qed.

Lemma rhs_eval_to_exten:
  forall r v,
  rhs_eval_to valu1 ge sp m r v ->
  (forall v, In v (valnums_rhs r) -> Plt v upto) ->
  rhs_eval_to valu2 ge sp m r v.
Proof.
  intros. inv H; simpl in *.
- constructor. rewrite valnums_val_exten by assumption. auto.
- econstructor; eauto. rewrite valnums_val_exten by assumption. auto.
Qed.

Lemma equation_holds_exten:
  forall e,
  equation_holds valu1 ge sp m e ->
  wf_equation upto e ->
  equation_holds valu2 ge sp m e.
Proof.
  intros. destruct e. destruct H0. inv H.
- constructor. rewrite AGREE by auto. apply rhs_eval_to_exten; auto.
- econstructor. apply rhs_eval_to_exten; eauto. rewrite AGREE by auto. auto.
Qed.

Lemma numbering_holds_exten:
  forall n,
  numbering_holds valu1 ge sp rs m n ->
  Ple n.(num_next) upto ->
  numbering_holds valu2 ge sp rs m n.
Proof.
  intros. destruct H. constructor; intros.
- auto.
- apply equation_holds_exten. auto.
  eapply wf_equation_incr; eauto with cse.
- rewrite AGREE. eauto. eapply Pos.lt_le_trans; eauto. eapply wf_num_reg; eauto.
Qed.

End EXTEN.

Ltac splitall := repeat (match goal with |- _ /\ _ => split end).

Lemma valnum_reg_holds:
  forall valu1 ge sp rs m n r n' v,
  numbering_holds valu1 ge sp rs m n ->
  valnum_reg n r = (n', v) ->
  exists valu2,
     numbering_holds valu2 ge sp rs m n'
  /\ rs#r = valu2 v
  /\ valu_agree valu1 valu2 n.(num_next)
  /\ Plt v n'.(num_next)
  /\ Ple n.(num_next) n'.(num_next).
Proof.
  unfold valnum_reg; intros.
  destruct (num_reg n)!r as [v'|] eqn:NR.
- inv H0. exists valu1; splitall.
  + auto.
  + eauto with cse.
  + red; auto.
  + eauto with cse.
  + apply Ple_refl.
- inv H0; simpl.
  set (valu2 := fun vn => if peq vn n.(num_next) then rs#r else valu1 vn).
  assert (AG: valu_agree valu1 valu2 n.(num_next)).
  { red; intros. unfold valu2. apply peq_false. apply Plt_ne; auto. }
  exists valu2; splitall.
+ constructor; simpl; intros.
* constructor; simpl; intros.
  apply wf_equation_incr with (num_next n). eauto with cse. xomega.
  rewrite PTree.gsspec in H0. destruct (peq r0 r).
  inv H0; xomega.
  apply Plt_trans_succ; eauto with cse.
  rewrite PMap.gsspec in H0. destruct (peq v (num_next n)).
  replace r0 with r by (simpl in H0; intuition). rewrite PTree.gss. subst; auto.
  exploit wf_num_val; eauto with cse. intro.
  rewrite PTree.gso by congruence. auto.
* eapply equation_holds_exten; eauto with cse.
* unfold valu2. rewrite PTree.gsspec in H0. destruct (peq r0 r).
  inv H0. rewrite peq_true; auto.
  rewrite peq_false. eauto with cse. apply Plt_ne; eauto with cse.
+ unfold valu2. rewrite peq_true; auto.
+ auto.
+ xomega.
+ xomega.
Qed.

Lemma valnum_regs_holds:
  forall rl valu1 ge sp rs m n n' vl,
  numbering_holds valu1 ge sp rs m n ->
  valnum_regs n rl = (n', vl) ->
  exists valu2,
     numbering_holds valu2 ge sp rs m n'
  /\ rs##rl = map valu2 vl
  /\ valu_agree valu1 valu2 n.(num_next)
  /\ (forall v, In v vl -> Plt v n'.(num_next))
  /\ Ple n.(num_next) n'.(num_next).
Proof.
  induction rl; simpl; intros.
- inv H0. exists valu1; splitall; auto. red; auto. simpl; tauto. xomega.
- destruct (valnum_reg n a) as [n1 v1] eqn:V1.
  destruct (valnum_regs n1 rl) as [n2 vs] eqn:V2.
  inv H0.
  exploit valnum_reg_holds; eauto.
  intros (valu2 & A & B & C & D & E).
  exploit (IHrl valu2); eauto.
  intros (valu3 & P & Q & R & S & T).
  exists valu3; splitall.
  + auto.
  + simpl; f_equal; auto. rewrite R; auto.
  + red; intros. transitivity (valu2 v); auto. apply R. xomega.
  + simpl; intros. destruct H0; auto. subst v1; xomega.
  + xomega.
Qed.

Lemma find_valnum_rhs_charact:
  forall rh v eqs,
  find_valnum_rhs rh eqs = Some v -> In (Eq v true rh) eqs.
Proof.
  induction eqs; simpl; intros.
- inv H.
- destruct a. destruct (strict && eq_rhs rh r) eqn:T.
  + InvBooleans. inv H. left; auto.
  + right; eauto.
Qed.

Lemma find_valnum_rhs'_charact:
  forall rh v eqs,
  find_valnum_rhs' rh eqs = Some v -> exists strict, In (Eq v strict rh) eqs.
Proof.
  induction eqs; simpl; intros.
- inv H.
- destruct a. destruct (eq_rhs rh r) eqn:T.
  + inv H. exists strict; auto.
  + exploit IHeqs; eauto. intros [s IN]. exists s; auto.
Qed.

Lemma find_valnum_num_charact:
  forall v r eqs, find_valnum_num v eqs = Some r -> In (Eq v true r) eqs.
Proof.
  induction eqs; simpl; intros.
- inv H.
- destruct a. destruct (strict && peq v v0) eqn:T.
  + InvBooleans. inv H. auto.
  + eauto.
Qed.

Lemma reg_valnum_sound:
  forall n v r valu ge sp rs m,
  reg_valnum n v = Some r ->
  numbering_holds valu ge sp rs m n ->
  rs#r = valu v.
Proof.
  unfold reg_valnum; intros. destruct (num_val n)#v as [ | r1 rl] eqn:E; inv H.
  eapply num_holds_reg; eauto. eapply wf_num_val; eauto with cse.
  rewrite E; auto with coqlib.
Qed.

Lemma regs_valnums_sound:
  forall n valu ge sp rs m,
  numbering_holds valu ge sp rs m n ->
  forall vl rl,
  regs_valnums n vl = Some rl ->
  rs##rl = map valu vl.
Proof.
  induction vl; simpl; intros.
- inv H0; auto.
- destruct (reg_valnum n a) as [r1|] eqn:RV1; try discriminate.
  destruct (regs_valnums n vl) as [rl1|] eqn:RVL; inv H0.
  simpl; f_equal. eapply reg_valnum_sound; eauto. eauto.
Qed.

Lemma find_rhs_sound:
  forall n rh r valu ge sp rs m,
  find_rhs n rh = Some r ->
  numbering_holds valu ge sp rs m n ->
  exists v, rhs_eval_to valu ge sp m rh v /\ Val.lessdef v rs#r.
Proof.
  unfold find_rhs; intros. destruct (find_valnum_rhs' rh (num_eqs n)) as [vres|] eqn:E; try discriminate.
  exploit find_valnum_rhs'_charact; eauto. intros [strict IN].
  erewrite reg_valnum_sound by eauto.
  exploit num_holds_eq; eauto. intros EH. inv EH.
- exists (valu vres); auto.
- exists v; auto.
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

Lemma forget_reg_charact:
  forall n rd r v,
  wf_numbering n ->
  In r (PMap.get v (forget_reg n rd)) -> r <> rd /\ In r (PMap.get v n.(num_val)).
Proof.
  unfold forget_reg; intros.
  destruct (PTree.get rd n.(num_reg)) as [vd|] eqn:GET.
- rewrite PMap.gsspec in H0. destruct (peq v vd).
  + subst v. rewrite in_remove in H0. intuition.
  + split; auto. exploit wf_num_val; eauto. congruence.
- split; auto. exploit wf_num_val; eauto. congruence.
Qed.

Lemma update_reg_charact:
  forall n rd vd r v,
  wf_numbering n ->
  In r (PMap.get v (update_reg n rd vd)) ->
  PTree.get r (PTree.set rd vd n.(num_reg)) = Some v.
Proof.
  unfold update_reg; intros.
  rewrite PMap.gsspec in H0.
  destruct (peq v vd).
- subst v. destruct H0.
+ subst r. apply PTree.gss.
+ exploit forget_reg_charact; eauto. intros [A B].
  rewrite PTree.gso by auto. eapply wf_num_val; eauto.
- exploit forget_reg_charact; eauto. intros [A B].
  rewrite PTree.gso by auto. eapply wf_num_val; eauto.
Qed.

Lemma rhs_eval_to_inj:
  forall valu ge sp m rh v1 v2,
  rhs_eval_to valu ge sp m rh v1 -> rhs_eval_to valu ge sp m rh v2 -> v1 = v2.
Proof.
  intros. inv H; inv H0; congruence.
Qed.

Lemma add_rhs_holds:
  forall valu1 ge sp rs m n rd rh rs',
  numbering_holds valu1 ge sp rs m n ->
  rhs_eval_to valu1 ge sp m rh (rs'#rd) ->
  wf_rhs n.(num_next) rh ->
  (forall r, r <> rd -> rs'#r = rs#r) ->
  exists valu2, numbering_holds valu2 ge sp rs' m (add_rhs n rd rh).
Proof.
  unfold add_rhs; intros.
  destruct (find_valnum_rhs rh n.(num_eqs)) as [vres|] eqn:FIND.

- (* A value number exists already *)
  exploit find_valnum_rhs_charact; eauto. intros IN.
  exploit wf_num_eqs; eauto with cse. intros [A B].
  exploit num_holds_eq; eauto. intros EH. inv EH.
  assert (rs'#rd = valu1 vres) by (eapply rhs_eval_to_inj; eauto).
  exists valu1; constructor; simpl; intros.
+ constructor; simpl; intros.
  * eauto with cse.
  * rewrite PTree.gsspec in H5. destruct (peq r rd).
    inv H5. auto.
    eauto with cse.
  * eapply update_reg_charact; eauto with cse.
+ eauto with cse.
+ rewrite PTree.gsspec in H5. destruct (peq r rd).
  congruence.
  rewrite H2 by auto. eauto with cse.

- (* Assigning a new value number *)
  set (valu2 := fun v => if peq v n.(num_next) then rs'#rd else valu1 v).
  assert (AG: valu_agree valu1 valu2 n.(num_next)).
  { red; intros. unfold valu2. apply peq_false. apply Plt_ne; auto. }
  exists valu2; constructor; simpl; intros.
+ constructor; simpl; intros.
  * destruct H3. inv H3. simpl; split. xomega.
    red; intros. apply Plt_trans_succ; eauto.
    apply wf_equation_incr with (num_next n). eauto with cse. xomega.
  * rewrite PTree.gsspec in H3. destruct (peq r rd).
    inv H3. xomega.
    apply Plt_trans_succ; eauto with cse.
  * apply update_reg_charact; eauto with cse.
+ destruct H3. inv H3.
  constructor. unfold valu2 at 2; rewrite peq_true.
  eapply rhs_eval_to_exten; eauto.
  eapply equation_holds_exten; eauto with cse.
+ rewrite PTree.gsspec in H3. unfold valu2. destruct (peq r rd).
  inv H3. rewrite peq_true; auto.
  rewrite peq_false. rewrite H2 by auto. eauto with cse.
  apply Plt_ne; eauto with cse.
Qed.

Lemma add_op_holds:
  forall valu1 ge sp rs m n op (args: list reg) v dst,
  numbering_holds valu1 ge sp rs m n ->
  eval_operation ge sp op rs##args m = Some v ->
  exists valu2, numbering_holds valu2 ge sp (rs#dst <- v) m (add_op n dst op args).
Proof.
  unfold add_op; intros.
  destruct (is_move_operation op args) as [src|] eqn:ISMOVE.
- (* special case for moves *)
  exploit is_move_operation_correct; eauto. intros [A B]; subst op args.
  simpl in H0. inv H0.
  destruct (valnum_reg n src) as [n1 vsrc] eqn:VN.
  exploit valnum_reg_holds; eauto.
  intros (valu2 & A & B & C & D & E).
  exists valu2; constructor; simpl; intros.
+ constructor; simpl; intros; eauto with cse.
  * rewrite PTree.gsspec in H0. destruct (peq r dst).
    inv H0. auto.
    eauto with cse.
  * eapply update_reg_charact; eauto with cse.
+ eauto with cse.
+ rewrite PTree.gsspec in H0. rewrite Regmap.gsspec.
  destruct (peq r dst). congruence. eauto with cse.

- (* general case *)
  destruct (valnum_regs n args) as [n1 vl] eqn:VN.
  exploit valnum_regs_holds; eauto.
  intros (valu2 & A & B & C & D & E).
  eapply add_rhs_holds; eauto.
+ constructor. rewrite Regmap.gss. congruence.
+ intros. apply Regmap.gso; auto.
Qed.

Lemma add_load_holds:
  forall valu1 ge sp rs m n addr (args: list reg) a chunk v dst,
  numbering_holds valu1 ge sp rs m n ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists valu2, numbering_holds valu2 ge sp (rs#dst <- v) m (add_load n dst chunk addr args).
Proof.
  unfold add_load; intros.
  destruct (valnum_regs n args) as [n1 vl] eqn:VN.
  exploit valnum_regs_holds; eauto.
  intros (valu2 & A & B & C & D & E).
  eapply add_rhs_holds; eauto.
+ econstructor. rewrite <- B; eauto. rewrite Regmap.gss; auto.
+ intros. apply Regmap.gso; auto.
Qed.

Lemma set_unknown_holds:
  forall valu ge sp rs m n r v,
  numbering_holds valu ge sp rs m n ->
  numbering_holds valu ge sp (rs#r <- v) m (set_unknown n r).
Proof.
  intros; constructor; simpl; intros.
- constructor; simpl; intros.
  + eauto with cse.
  + rewrite PTree.grspec in H0. destruct (PTree.elt_eq r0 r).
    discriminate.
    eauto with cse.
  + exploit forget_reg_charact; eauto with cse. intros [A B].
    rewrite PTree.gro; eauto with cse.
- eauto with cse.
- rewrite PTree.grspec in H0. destruct (PTree.elt_eq r0 r).
  discriminate.
  rewrite Regmap.gso; eauto with cse.
Qed.

Lemma set_res_unknown_holds:
  forall valu ge sp rs m n r v,
  numbering_holds valu ge sp rs m n ->
  numbering_holds valu ge sp (regmap_setres r v rs) m (set_res_unknown n r).
Proof.
  intros. destruct r; simpl; auto. apply set_unknown_holds; auto.
Qed.

Lemma kill_eqs_charact:
  forall pred l strict r eqs,
  In (Eq l strict r) (kill_eqs pred eqs) ->
  pred r = false /\ In (Eq l strict r) eqs.
Proof.
  induction eqs; simpl; intros.
- tauto.
- destruct a. destruct (pred r0) eqn:PRED.
  tauto.
  inv H. inv H0. auto. tauto.
Qed.

Lemma kill_equations_hold:
  forall valu ge sp rs m n pred m',
  numbering_holds valu ge sp rs m n ->
  (forall r v,
      pred r = false ->
      rhs_eval_to valu ge sp m r v ->
      rhs_eval_to valu ge sp m' r v) ->
  numbering_holds valu ge sp rs m' (kill_equations pred n).
Proof.
  intros; constructor; simpl; intros.
- constructor; simpl; intros; eauto with cse.
  destruct e. exploit kill_eqs_charact; eauto. intros [A B]. eauto with cse.
- destruct eq. exploit kill_eqs_charact; eauto. intros [A B].
  exploit num_holds_eq; eauto. intro EH; inv EH; econstructor; eauto.
- eauto with cse.
Qed.

Lemma kill_all_loads_hold:
  forall valu ge sp rs m n m',
  numbering_holds valu ge sp rs m n ->
  numbering_holds valu ge sp rs m' (kill_all_loads n).
Proof.
  intros. eapply kill_equations_hold; eauto.
  unfold filter_loads; intros. inv H1.
  constructor. rewrite <- H2. apply op_depends_on_memory_correct; auto.
  discriminate.
Qed.

Lemma kill_loads_after_store_holds:
  forall valu ge sp rs m n addr args a chunk v m' bc approx ae am,
  numbering_holds valu ge (Vptr sp Ptrofs.zero) rs m n ->
  eval_addressing ge (Vptr sp Ptrofs.zero) addr rs##args = Some a ->
  Mem.storev chunk m a v = Some m' ->
  genv_match bc ge ->
  bc sp = BCstack ->
  ematch bc rs ae ->
  approx = VA.State ae am ->
  numbering_holds valu ge (Vptr sp Ptrofs.zero) rs m'
                           (kill_loads_after_store approx n chunk addr args).
Proof.
  intros. apply kill_equations_hold with m; auto.
  intros. unfold filter_after_store in H6; inv H7.
- constructor. rewrite <- H8. apply op_depends_on_memory_correct; auto.
- destruct (regs_valnums n vl) as [rl|] eqn:RV; try discriminate.
  econstructor; eauto. rewrite <- H9.
  destruct a; simpl in H1; try discriminate.
  destruct a0; simpl in H9; try discriminate.
  simpl.
  rewrite negb_false_iff in H6. unfold aaddressing in H6.
  eapply Mem.load_store_other. eauto.
  eapply pdisjoint_sound. eauto.
  apply match_aptr_of_aval. eapply eval_static_addressing_sound; eauto.
  erewrite <- regs_valnums_sound by eauto. eauto with va.
  apply match_aptr_of_aval. eapply eval_static_addressing_sound; eauto with va.
Qed.

Lemma store_normalized_range_sound:
  forall bc chunk v,
  vmatch bc v (store_normalized_range chunk) ->
  Val.lessdef (Val.load_result chunk v) v.
Proof.
  intros. unfold Val.load_result; remember Archi.ptr64 as ptr64.
  destruct chunk; simpl in *; destruct v; auto.
- inv H. rewrite is_sgn_sign_ext in H4 by omega. rewrite H4; auto.
- inv H. rewrite is_uns_zero_ext in H4 by omega. rewrite H4; auto.
- inv H. rewrite is_sgn_sign_ext in H4 by omega. rewrite H4; auto.
- inv H. rewrite is_uns_zero_ext in H4 by omega. rewrite H4; auto.
- destruct ptr64; auto.
- destruct ptr64; auto.
- destruct ptr64; auto.
Qed.

Lemma add_store_result_hold:
  forall valu1 ge sp rs m' n addr args a chunk m src bc ae approx am,
  numbering_holds valu1 ge sp rs m' n ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.storev chunk m a rs#src = Some m' ->
  ematch bc rs ae ->
  approx = VA.State ae am ->
  exists valu2, numbering_holds valu2 ge sp rs m' (add_store_result approx n chunk addr args src).
Proof.
  unfold add_store_result; intros.
  unfold avalue; rewrite H3.
  destruct (vincl (AE.get src ae) (store_normalized_range chunk)) eqn:INCL.
- destruct (valnum_reg n src) as [n1 vsrc] eqn:VR1.
  destruct (valnum_regs n1 args) as [n2 vargs] eqn:VR2.
  exploit valnum_reg_holds; eauto. intros (valu2 & A & B & C & D & E).
  exploit valnum_regs_holds; eauto. intros (valu3 & P & Q & R & S & T).
  exists valu3. constructor; simpl; intros.
+ constructor; simpl; intros; eauto with cse.
  destruct H4; eauto with cse. subst e. split.
  eapply Pos.lt_le_trans; eauto.
  red; simpl; intros. auto.
+ destruct H4; eauto with cse. subst eq. apply eq_holds_lessdef with (Val.load_result chunk rs#src).
  apply load_eval_to with a. rewrite <- Q; auto.
  destruct a; try discriminate. simpl. eapply Mem.load_store_same; eauto.
  rewrite B. rewrite R by auto. apply store_normalized_range_sound with bc.
  rewrite <- B. eapply vmatch_ge. apply vincl_ge; eauto. apply H2.
+ eauto with cse.

- exists valu1; auto.
Qed.

Lemma kill_loads_after_storebytes_holds:
  forall valu ge sp rs m n dst b ofs bytes m' bc approx ae am sz,
  numbering_holds valu ge (Vptr sp Ptrofs.zero) rs m n ->
  pmatch bc b ofs dst ->
  Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
  genv_match bc ge ->
  bc sp = BCstack ->
  ematch bc rs ae ->
  approx = VA.State ae am ->
  length bytes = nat_of_Z sz -> sz >= 0 ->
  numbering_holds valu ge (Vptr sp Ptrofs.zero) rs m'
                           (kill_loads_after_storebytes approx n dst sz).
Proof.
  intros. apply kill_equations_hold with m; auto.
  intros. unfold filter_after_store in H8; inv H9.
- constructor. rewrite <- H10. apply op_depends_on_memory_correct; auto.
- destruct (regs_valnums n vl) as [rl|] eqn:RV; try discriminate.
  econstructor; eauto. rewrite <- H11.
  destruct a; simpl in H10; try discriminate.
  simpl.
  rewrite negb_false_iff in H8.
  eapply Mem.load_storebytes_other. eauto.
  rewrite H6. rewrite nat_of_Z_eq by auto.
  eapply pdisjoint_sound. eauto.
  unfold aaddressing. apply match_aptr_of_aval. eapply eval_static_addressing_sound; eauto.
  erewrite <- regs_valnums_sound by eauto. eauto with va.
  auto.
Qed.

Lemma load_memcpy:
  forall m b1 ofs1 sz bytes b2 ofs2 m' chunk i v,
  Mem.loadbytes m b1 ofs1 sz = Some bytes ->
  Mem.storebytes m b2 ofs2 bytes = Some m' ->
  Mem.load chunk m b1 i = Some v ->
  ofs1 <= i -> i + size_chunk chunk <= ofs1 + sz ->
  (align_chunk chunk | ofs2 - ofs1) ->
  Mem.load chunk m' b2 (i + (ofs2 - ofs1)) = Some v.
Proof.
  intros.
  generalize (size_chunk_pos chunk); intros SPOS.
  set (n1 := i - ofs1).
  set (n2 := size_chunk chunk).
  set (n3 := sz - (n1 + n2)).
  replace sz with (n1 + (n2 + n3)) in H by (unfold n3, n2, n1; omega).
  exploit Mem.loadbytes_split; eauto.
  unfold n1; omega.
  unfold n3, n2, n1; omega.
  intros (bytes1 & bytes23 & LB1 & LB23 & EQ).
  clear H.
  exploit Mem.loadbytes_split; eauto.
  unfold n2; omega.
  unfold n3, n2, n1; omega.
  intros (bytes2 & bytes3 & LB2 & LB3 & EQ').
  subst bytes23; subst bytes.
  exploit Mem.load_loadbytes; eauto. intros (bytes2' & A & B).
  assert (bytes2' = bytes2).
  { replace (ofs1 + n1) with i in LB2 by (unfold n1; omega). unfold n2 in LB2. congruence.  }
  subst bytes2'.
  exploit Mem.storebytes_split; eauto. intros (m1 & SB1 & SB23).
  clear H0.
  exploit Mem.storebytes_split; eauto. intros (m2 & SB2 & SB3).
  clear SB23.
  assert (L1: Z.of_nat (length bytes1) = n1).
  { erewrite Mem.loadbytes_length by eauto. apply nat_of_Z_eq. unfold n1; omega. }
  assert (L2: Z.of_nat (length bytes2) = n2).
  { erewrite Mem.loadbytes_length by eauto. apply nat_of_Z_eq. unfold n2; omega. }
  rewrite L1 in *. rewrite L2 in *.
  assert (LB': Mem.loadbytes m2 b2 (ofs2 + n1) n2 = Some bytes2).
  { rewrite <- L2. eapply Mem.loadbytes_storebytes_same; eauto. }
  assert (LB'': Mem.loadbytes m' b2 (ofs2 + n1) n2 = Some bytes2).
  { rewrite <- LB'. eapply Mem.loadbytes_storebytes_other; eauto.
    unfold n2; omega.
    right; left; omega. }
  exploit Mem.load_valid_access; eauto. intros [P Q].
  rewrite B. apply Mem.loadbytes_load.
  replace (i + (ofs2 - ofs1)) with (ofs2 + n1) by (unfold n1; omega).
  exact LB''.
  apply Z.divide_add_r; auto.
Qed.

Lemma shift_memcpy_eq_wf:
  forall src sz delta e e' next,
  shift_memcpy_eq src sz delta e = Some e' ->
  wf_equation next e ->
  wf_equation next e'.
Proof with (try discriminate).
  unfold shift_memcpy_eq; intros.
  destruct e. destruct r... destruct a...
  try (rename i into ofs).
  destruct (zle src (Ptrofs.unsigned ofs) &&
        zle (Ptrofs.unsigned ofs + size_chunk m) (src + sz) &&
        zeq (delta mod align_chunk m) 0 && zle 0 (Ptrofs.unsigned ofs + delta) &&
        zle (Ptrofs.unsigned ofs + delta) Ptrofs.max_unsigned)...
  inv H. destruct H0. split. auto. red; simpl; tauto.
Qed.

Lemma shift_memcpy_eq_holds:
  forall src dst sz e e' m sp bytes m' valu ge,
  shift_memcpy_eq src sz (dst - src) e = Some e' ->
  Mem.loadbytes m sp src sz = Some bytes ->
  Mem.storebytes m sp dst bytes = Some m' ->
  equation_holds valu ge (Vptr sp Ptrofs.zero) m e ->
  equation_holds valu ge (Vptr sp Ptrofs.zero) m' e'.
Proof with (try discriminate).
  intros. set (delta := dst - src) in *. unfold shift_memcpy_eq in H.
  destruct e as [l strict rhs] eqn:E.
  destruct rhs as [op vl | chunk addr vl]...
  destruct addr...
  try (rename i into ofs).
  set (i1 := Ptrofs.unsigned ofs) in *. set (j := i1 + delta) in *.
  destruct (zle src i1)...
  destruct (zle (i1 + size_chunk chunk) (src + sz))...
  destruct (zeq (delta mod align_chunk chunk) 0)...
  destruct (zle 0 j)...
  destruct (zle j Ptrofs.max_unsigned)...
  simpl in H; inv H.
  assert (LD: forall v,
    Mem.loadv chunk m (Vptr sp ofs) = Some v ->
    Mem.loadv chunk m' (Vptr sp (Ptrofs.repr j)) = Some v).
  {
    simpl; intros. rewrite Ptrofs.unsigned_repr by omega.
    unfold j, delta. eapply load_memcpy; eauto.
    apply Zmod_divide; auto. generalize (align_chunk_pos chunk); omega.
  }
  inv H2.
+ inv H3. exploit eval_addressing_Ainstack_inv; eauto. intros [E1 E2].
  simpl in E2; rewrite Ptrofs.add_zero_l in E2. subst a.
  apply eq_holds_strict. econstructor. rewrite eval_addressing_Ainstack.
  simpl. rewrite Ptrofs.add_zero_l. eauto.
  apply LD; auto.
+ inv H4. exploit eval_addressing_Ainstack_inv; eauto. intros [E1 E2].
  simpl in E2; rewrite Ptrofs.add_zero_l in E2. subst a.
  apply eq_holds_lessdef with v; auto.
  econstructor. rewrite eval_addressing_Ainstack. simpl. rewrite Ptrofs.add_zero_l. eauto.
  apply LD; auto.
Qed.

Lemma add_memcpy_eqs_charact:
  forall e' src sz delta eqs2 eqs1,
  In e' (add_memcpy_eqs src sz delta eqs1 eqs2) ->
  In e' eqs2 \/ exists e, In e eqs1 /\ shift_memcpy_eq src sz delta e = Some e'.
Proof.
  induction eqs1; simpl; intros.
- auto.
- destruct (shift_memcpy_eq src sz delta a) as [e''|] eqn:SHIFT.
  + destruct H. subst e''. right; exists a; auto.
    destruct IHeqs1 as [A | [e [A B]]]; auto. right; exists e; auto.
  + destruct IHeqs1 as [A | [e [A B]]]; auto. right; exists e; auto.
Qed.

Lemma add_memcpy_holds:
  forall m bsrc osrc sz bytes bdst odst m' valu ge sp rs n1 n2 bc asrc adst,
  Mem.loadbytes m bsrc (Ptrofs.unsigned osrc) sz = Some bytes ->
  Mem.storebytes m bdst (Ptrofs.unsigned odst) bytes = Some m' ->
  numbering_holds valu ge (Vptr sp Ptrofs.zero) rs m n1 ->
  numbering_holds valu ge (Vptr sp Ptrofs.zero) rs m' n2 ->
  pmatch bc bsrc osrc asrc ->
  pmatch bc bdst odst adst ->
  bc sp = BCstack ->
  Ple (num_next n1) (num_next n2) ->
  numbering_holds valu ge (Vptr sp Ptrofs.zero) rs m' (add_memcpy n1 n2 asrc adst sz).
Proof.
  intros. unfold add_memcpy.
  destruct asrc; auto; destruct adst; auto.
  assert (A: forall b o i, pmatch bc b o (Stk i) -> b = sp /\ i = o).
  {
    intros. inv H7. split; auto. eapply bc_stack; eauto.
  }
  apply A in H3; destruct H3. subst bsrc ofs.
  apply A in H4; destruct H4. subst bdst ofs0.
  constructor; simpl; intros; eauto with cse.
- constructor; simpl; eauto with cse.
  intros. exploit add_memcpy_eqs_charact; eauto. intros [X | (e0 & X & Y)].
  eauto with cse.
  apply wf_equation_incr with (num_next n1); auto.
  eapply shift_memcpy_eq_wf; eauto with cse.
- exploit add_memcpy_eqs_charact; eauto. intros [X | (e0 & X & Y)].
  eauto with cse.
  eapply shift_memcpy_eq_holds; eauto with cse.
Qed.

(** Correctness of operator reduction *)

Section REDUCE.

Variable A: Type.
Variable f: (valnum -> option rhs) -> A -> list valnum -> option (A * list valnum).
Variable V: Type.
Variable ge: genv.
Variable sp: val.
Variable rs: regset.
Variable m: mem.
Variable sem: A -> list val -> option V.
Hypothesis f_sound:
  forall eqs valu op args op' args',
  (forall v rhs, eqs v = Some rhs -> rhs_eval_to valu ge sp m rhs (valu v)) ->
  f eqs op args = Some(op', args') ->
  sem op' (map valu args') = sem op (map valu args).
Variable n: numbering.
Variable valu: valnum -> val.
Hypothesis n_holds: numbering_holds valu ge sp rs m n.

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
    simpl; intros.
    exploit num_holds_eq; eauto.
    eapply find_valnum_num_charact; eauto with cse.
    intros EH; inv EH; auto.
  destruct (reduce_rec A f n niter op1 args1) as [[op2 rl2] | ] eqn:?.
  inv H. eapply IHniter; eauto.
  destruct (regs_valnums n args1) as [rl|] eqn:?.
  inv H. erewrite regs_valnums_sound; eauto.
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

(** The numberings associated to each instruction by the static analysis
  are inductively satisfiable, in the following sense: the numbering
  at the function entry point is satisfiable, and for any RTL execution
  from [pc] to [pc'], satisfiability at [pc] implies
  satisfiability at [pc']. *)

Theorem analysis_correct_1:
  forall ge sp rs m f vapprox approx pc pc' i,
  analyze f vapprox = Some approx ->
  f.(fn_code)!pc = Some i -> In pc' (successors_instr i) ->
  (exists valu, numbering_holds valu ge sp rs m (transfer f vapprox pc approx!!pc)) ->
  (exists valu, numbering_holds valu ge sp rs m approx!!pc').
Proof.
  intros.
  assert (Numbering.ge approx!!pc' (transfer f vapprox pc approx!!pc)).
    eapply Solver.fixpoint_solution; eauto.
  destruct H2 as [valu NH]. exists valu; apply H3. auto.
Qed.

Theorem analysis_correct_entry:
  forall ge sp rs m f vapprox approx,
  analyze f vapprox = Some approx ->
  exists valu, numbering_holds valu ge sp rs m approx!!(f.(fn_entrypoint)).
Proof.
  intros.
  replace (approx!!(f.(fn_entrypoint))) with Solver.L.top.
  exists (fun v => Vundef). apply empty_numbering_holds.
  symmetry. eapply Solver.fixpoint_entry; eauto.
Qed.

(** * Semantic preservation *)

Section PRESERVATION.

Variable prog: program.
Variable tprog : program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  exists cu tf, Genv.find_funct tge v = Some tf /\ transf_fundef (romem_for cu) f = OK tf /\ linkorder cu prog.
Proof (Genv.find_funct_match TRANSF).

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cu tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef (romem_for cu) f = OK tf /\ linkorder cu prog.
Proof (Genv.find_funct_ptr_match TRANSF).

Lemma sig_preserved:
  forall rm f tf, transf_fundef rm f = OK tf -> funsig tf = funsig f.
Proof.
  unfold transf_fundef; intros. destruct f; monadInv H; auto.
  unfold transf_function in EQ.
  destruct (analyze f (vanalyze rm f)); try discriminate. inv EQ; auto.
Qed.

Definition transf_function' (f: function) (approxs: PMap.t numbering) : function :=
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (transf_code approxs f.(fn_code))
    f.(fn_entrypoint).

Definition regs_lessdef (rs1 rs2: regset) : Prop :=
  forall r, Val.lessdef (rs1#r) (rs2#r).

Lemma regs_lessdef_regs:
  forall rs1 rs2, regs_lessdef rs1 rs2 ->
  forall rl, Val.lessdef_list rs1##rl rs2##rl.
Proof.
  induction rl; constructor; auto.
Qed.

Lemma set_reg_lessdef:
  forall r v1 v2 rs1 rs2,
  Val.lessdef v1 v2 -> regs_lessdef rs1 rs2 -> regs_lessdef (rs1#r <- v1) (rs2#r <- v2).
Proof.
  intros; red; intros. repeat rewrite Regmap.gsspec.
  destruct (peq r0 r); auto.
Qed.

Lemma init_regs_lessdef:
  forall rl vl1 vl2,
  Val.lessdef_list vl1 vl2 ->
  regs_lessdef (init_regs vl1 rl) (init_regs vl2 rl).
Proof.
  induction rl; simpl; intros.
  red; intros. rewrite Regmap.gi. auto.
  inv H. red; intros. rewrite Regmap.gi. auto.
  apply set_reg_lessdef; auto.
Qed.

Lemma find_function_translated:
  forall ros rs fd rs',
  find_function ge ros rs = Some fd ->
  regs_lessdef rs rs' ->
  exists cu tfd, find_function tge ros rs' = Some tfd
              /\ transf_fundef (romem_for cu) fd = OK tfd
              /\ linkorder cu prog.
Proof.
  unfold find_function; intros; destruct ros.
- specialize (H0 r). inv H0.
  apply functions_translated; auto.
  rewrite <- H2 in H; discriminate.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

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

Definition analyze (cu: program) (f: function) :=
  CSE.analyze f (vanalyze (romem_for cu) f).

Inductive match_stackframes: list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes nil nil
  | match_stackframes_cons:
      forall res sp pc rs f s rs' s' cu approx
           (LINK: linkorder cu prog)
           (ANALYZE: analyze cu f = Some approx)
           (SAT: forall v m, exists valu, numbering_holds valu ge sp (rs#res <- v) m approx!!pc)
           (RLD: regs_lessdef rs rs')
           (STACKS: match_stackframes s s'),
    match_stackframes
      (Stackframe res f sp pc rs :: s)
      (Stackframe res (transf_function' f approx) sp pc rs' :: s').

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m s' rs' m' f cu approx
             (LINK: linkorder cu prog)
             (ANALYZE: analyze cu f = Some approx)
             (SAT: exists valu, numbering_holds valu ge sp rs m approx!!pc)
             (RLD: regs_lessdef rs rs')
             (MEXT: Mem.extends m m')
             (STACKS: match_stackframes s s'),
      match_states (State s f sp pc rs m)
                   (State s' (transf_function' f approx) sp pc rs' m')
  | match_states_call:
      forall s f tf args m s' args' m' cu
             (LINK: linkorder cu prog)
             (STACKS: match_stackframes s s')
             (TFD: transf_fundef (romem_for cu) f = OK tf)
             (ARGS: Val.lessdef_list args args')
             (MEXT: Mem.extends m m'),
      match_states (Callstate s f args m)
                   (Callstate s' tf args' m')
  | match_states_return:
      forall s s' v v' m m'
             (STACK: match_stackframes s s')
             (RES: Val.lessdef v v')
             (MEXT: Mem.extends m m'),
      match_states (Returnstate s v m)
                   (Returnstate s' v' m').

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
  forall s1' (MS: match_states s1 s1') (SOUND: sound_state prog s1),
  exists s2', step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; inv MS; try (TransfInstr; intro C).

  (* Inop *)
- econstructor; split.
  eapply exec_Inop; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H; auto.

  (* Iop *)
- destruct (is_trivial_op op) eqn:TRIV.
+ (* unchanged *)
  exploit eval_operation_lessdef. eapply regs_lessdef_regs; eauto. eauto. eauto.
  intros [v' [A B]].
  econstructor; split.
  eapply exec_Iop with (v := v'); eauto.
  rewrite <- A. apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  destruct SAT as [valu NH]. eapply add_op_holds; eauto.
  apply set_reg_lessdef; auto.
+ (* possibly optimized *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (find_rhs n1 (Op op vl)) as [r|] eqn:?.
* (* replaced by move *)
  exploit find_rhs_sound; eauto. intros (v' & EV & LD).
  assert (v' = v) by (inv EV; congruence). subst v'.
  econstructor; split.
  eapply exec_Iop; eauto. simpl; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  eapply add_op_holds; eauto.
  apply set_reg_lessdef; auto.
  eapply Val.lessdef_trans; eauto.
* (* possibly simplified *)
  destruct (reduce operation combine_op n1 op args vl) as [op' args'] eqn:?.
  assert (RES: eval_operation ge sp op' rs##args' m = Some v).
    eapply reduce_sound with (sem := fun op vl => eval_operation ge sp op vl m); eauto.
    intros; eapply combine_op_sound; eauto.
  exploit eval_operation_lessdef. eapply regs_lessdef_regs; eauto. eauto. eauto.
  intros [v' [A B]].
  econstructor; split.
  eapply exec_Iop with (v := v'); eauto.
  rewrite <- A. apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  eapply add_op_holds; eauto.
  apply set_reg_lessdef; auto.

- (* Iload *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (find_rhs n1 (Load chunk addr vl)) as [r|] eqn:?.
+ (* replaced by move *)
  exploit find_rhs_sound; eauto. intros (v' & EV & LD).
  assert (v' = v) by (inv EV; congruence). subst v'.
  econstructor; split.
  eapply exec_Iop; eauto. simpl; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  eapply add_load_holds; eauto.
  apply set_reg_lessdef; auto. eapply Val.lessdef_trans; eauto.
+ (* load is preserved, but addressing is possibly simplified *)
  destruct (reduce addressing combine_addr n1 addr args vl) as [addr' args'] eqn:?.
  assert (ADDR: eval_addressing ge sp addr' rs##args' = Some a).
  { eapply reduce_sound with (sem := fun addr vl => eval_addressing ge sp addr vl); eauto.
    intros; eapply combine_addr_sound; eauto. }
  exploit eval_addressing_lessdef. apply regs_lessdef_regs; eauto. eexact ADDR.
  intros [a' [A B]].
  assert (ADDR': eval_addressing tge sp addr' rs'##args' = Some a').
  { rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved. }
  exploit Mem.loadv_extends; eauto.
  intros [v' [X Y]].
  econstructor; split.
  eapply exec_Iload; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  eapply add_load_holds; eauto.
  apply set_reg_lessdef; auto.

- (* Istore *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (reduce addressing combine_addr n1 addr args vl) as [addr' args'] eqn:?.
  assert (ADDR: eval_addressing ge sp addr' rs##args' = Some a).
  { eapply reduce_sound with (sem := fun addr vl => eval_addressing ge sp addr vl); eauto.
    intros; eapply combine_addr_sound; eauto. }
  exploit eval_addressing_lessdef. apply regs_lessdef_regs; eauto. eexact ADDR.
  intros [a' [A B]].
  assert (ADDR': eval_addressing tge sp addr' rs'##args' = Some a').
  { rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved. }
  exploit Mem.storev_extends; eauto. intros [m'' [X Y]].
  econstructor; split.
  eapply exec_Istore; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  InvSoundState.
  eapply add_store_result_hold; eauto.
  eapply kill_loads_after_store_holds; eauto.

- (* Icall *)
  exploit find_function_translated; eauto. intros (cu' & tf & FIND' & TRANSF' & LINK').
  econstructor; split.
  eapply exec_Icall; eauto.
  eapply sig_preserved; eauto.
  econstructor; eauto.
  eapply match_stackframes_cons with (cu := cu); eauto.
  intros. eapply analysis_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  exists (fun _ => Vundef); apply empty_numbering_holds.
  apply regs_lessdef_regs; auto.

- (* Itailcall *)
  exploit find_function_translated; eauto. intros (cu' & tf & FIND' & TRANSF' & LINK').
  exploit Mem.free_parallel_extends; eauto. intros [m'' [A B]].
  econstructor; split.
  eapply exec_Itailcall; eauto.
  eapply sig_preserved; eauto.
  econstructor; eauto.
  apply regs_lessdef_regs; auto.

- (* Ibuiltin *)
  exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)); eauto.
  intros (vargs' & A & B).
  exploit external_call_mem_extends; eauto.
  intros (v' & m1' & P & Q & R & S).
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl; auto.
* unfold transfer; rewrite H.
  destruct SAT as [valu NH].
  assert (CASE1: exists valu, numbering_holds valu ge sp (regmap_setres res vres rs) m' empty_numbering).
  { exists valu; apply empty_numbering_holds. }
  assert (CASE2: m' = m -> exists valu, numbering_holds valu ge sp (regmap_setres res vres rs) m' (set_res_unknown approx#pc res)).
  { intros. subst m'. exists valu. apply set_res_unknown_holds; auto. }
  assert (CASE3: exists valu, numbering_holds valu ge sp (regmap_setres res vres rs) m'
                         (set_res_unknown (kill_all_loads approx#pc) res)).
  { exists valu. apply set_res_unknown_holds. eapply kill_all_loads_hold; eauto. }
  destruct ef.
  + apply CASE1.
  + apply CASE3.
  + apply CASE1.
  + apply CASE2; inv H1; auto.
  + apply CASE3.
  + apply CASE1.
  + apply CASE1.
  + inv H0; auto. inv H3; auto. inv H4; auto.
    simpl in H1. inv H1.
    exists valu.
    apply set_res_unknown_holds.
    InvSoundState. unfold vanalyze; rewrite AN.
    assert (pmatch bc bsrc osrc (aaddr_arg (VA.State ae am) a0))
    by (eapply aaddr_arg_sound_1; eauto).
    assert (pmatch bc bdst odst (aaddr_arg (VA.State ae am) a1))
    by (eapply aaddr_arg_sound_1; eauto).
    eapply add_memcpy_holds; eauto.
    eapply kill_loads_after_storebytes_holds; eauto.
    eapply Mem.loadbytes_length; eauto.
    simpl. apply Ple_refl.
  + apply CASE2; inv H1; auto.
  + apply CASE2; inv H1; auto.
  + apply CASE1.
  + apply CASE2; inv H1; auto.
* apply set_res_lessdef; auto.

- (* Icond *)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  elim SAT; intros valu1 NH1.
  exploit valnum_regs_holds; eauto. intros (valu2 & NH2 & EQ & AG & P & Q).
  destruct (reduce condition combine_cond n1 cond args vl) as [cond' args'] eqn:?.
  assert (RES: eval_condition cond' rs##args' m = Some b).
  { eapply reduce_sound with (sem := fun cond vl => eval_condition cond vl m); eauto.
    intros; eapply combine_cond_sound; eauto. }
  econstructor; split.
  eapply exec_Icond; eauto.
  eapply eval_condition_lessdef; eauto. apply regs_lessdef_regs; auto.
  econstructor; eauto.
  destruct b; eapply analysis_correct_1; eauto; simpl; auto;
  unfold transfer; rewrite H; auto.

- (* Ijumptable *)
  generalize (RLD arg); rewrite H0; intro LD; inv LD.
  econstructor; split.
  eapply exec_Ijumptable; eauto.
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl. eapply list_nth_z_in; eauto.
  unfold transfer; rewrite H; auto.

- (* Ireturn *)
  exploit Mem.free_parallel_extends; eauto. intros [m'' [A B]].
  econstructor; split.
  eapply exec_Ireturn; eauto.
  econstructor; eauto.
  destruct or; simpl; auto.

- (* internal function *)
  monadInv TFD. unfold transf_function in EQ. fold (analyze cu f) in EQ.
  destruct (analyze cu f) as [approx|] eqn:?; inv EQ.
  exploit Mem.alloc_extends; eauto. apply Z.le_refl. apply Z.le_refl.
  intros (m'' & A & B).
  econstructor; split.
  eapply exec_function_internal; simpl; eauto.
  simpl. econstructor; eauto.
  eapply analysis_correct_entry; eauto.
  apply init_regs_lessdef; auto.

- (* external function *)
  monadInv TFD.
  exploit external_call_mem_extends; eauto.
  intros (v' & m1' & P & Q & R & S).
  econstructor; split.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.

- (* return *)
  inv STACK.
  econstructor; split.
  eapply exec_return; eauto.
  econstructor; eauto.
  apply set_reg_lessdef; auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit funct_ptr_translated; eauto. intros (cu & tf & A & B & C).
  exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
  eapply (Genv.init_mem_match TRANSF); eauto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry. eapply match_program_main; eauto.
  rewrite <- H3. eapply sig_preserved; eauto.
  econstructor. eauto. constructor. auto. auto. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv RES. inv STACK. constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_step with
    (match_states := fun s1 s2 => sound_state prog s1 /\ match_states s1 s2).
- apply senv_preserved.
- intros. exploit transf_initial_states; eauto. intros [s2 [A B]].
  exists s2. split. auto. split. apply sound_initial; auto. auto.
- intros. destruct H. eapply transf_final_states; eauto.
- intros. destruct H0. exploit transf_step_correct; eauto.
  intros [s2' [A B]]. exists s2'; split. auto. split. eapply sound_step; eauto. auto.
Qed.

End PRESERVATION.

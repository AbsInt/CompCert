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

(** Correctness of instruction selection *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import Selection.

Open Local Scope selection_scope.

Section CMCONSTR.

Variable ge: genv.
Variable sp: val.
Variable e: env.
Variable m: mem.

(** * Lifting of let-bound variables *)

Inductive insert_lenv: letenv -> nat -> val -> letenv -> Prop :=
  | insert_lenv_0:
      forall le v,
      insert_lenv le O v (v :: le)
  | insert_lenv_S:
      forall le p w le' v,
      insert_lenv le p w le' ->
      insert_lenv (v :: le) (S p) w (v :: le').

Lemma insert_lenv_lookup1:
  forall le p w le',
  insert_lenv le p w le' ->
  forall n v,
  nth_error le n = Some v -> (p > n)%nat ->
  nth_error le' n = Some v.
Proof.
  induction 1; intros.
  omegaContradiction.
  destruct n; simpl; simpl in H0. auto. 
  apply IHinsert_lenv. auto. omega.
Qed.

Lemma insert_lenv_lookup2:
  forall le p w le',
  insert_lenv le p w le' ->
  forall n v,
  nth_error le n = Some v -> (p <= n)%nat ->
  nth_error le' (S n) = Some v.
Proof.
  induction 1; intros.
  simpl. assumption.
  simpl. destruct n. omegaContradiction. 
  apply IHinsert_lenv. exact H0. omega.
Qed.

Hint Resolve eval_Evar eval_Eop eval_Eload eval_Econdition
             eval_Elet eval_Eletvar 
             eval_CEtrue eval_CEfalse eval_CEcond
             eval_CEcondition eval_Enil eval_Econs: evalexpr.

Lemma eval_lift_expr:
  forall w le a v,
  eval_expr ge sp e m le a v ->
  forall p le', insert_lenv le p w le' ->
  eval_expr ge sp e m le' (lift_expr p a) v.
Proof.
  intro w.
  apply (eval_expr_ind3 ge sp e m
    (fun le a v =>
      forall p le', insert_lenv le p w le' ->
      eval_expr ge sp e m le' (lift_expr p a) v)
    (fun le a v =>
      forall p le', insert_lenv le p w le' ->
      eval_condexpr ge sp e m le' (lift_condexpr p a) v)
    (fun le al vl =>
      forall p le', insert_lenv le p w le' ->
      eval_exprlist ge sp e m le' (lift_exprlist p al) vl));
  simpl; intros; eauto with evalexpr.

  destruct v1; eapply eval_Econdition;
  eauto with evalexpr; simpl; eauto with evalexpr.

  eapply eval_Elet. eauto. apply H2. apply insert_lenv_S; auto.

  case (le_gt_dec p n); intro. 
  apply eval_Eletvar. eapply insert_lenv_lookup2; eauto.
  apply eval_Eletvar. eapply insert_lenv_lookup1; eauto.

  destruct vb1; eapply eval_CEcondition;
  eauto with evalexpr; simpl; eauto with evalexpr.
Qed.

Lemma eval_lift:
  forall le a v w,
  eval_expr ge sp e m le a v ->
  eval_expr ge sp e m (w::le) (lift a) v.
Proof.
  intros. unfold lift. eapply eval_lift_expr.
  eexact H. apply insert_lenv_0. 
Qed.

Hint Resolve eval_lift: evalexpr.

(** * Useful lemmas and tactics *)

(** The following are trivial lemmas and custom tactics that help
  perform backward (inversion) and forward reasoning over the evaluation
  of operator applications. *)  

Ltac EvalOp := eapply eval_Eop; eauto with evalexpr.

Ltac TrivialOp cstr := unfold cstr; intros; EvalOp.

Ltac InvEval1 :=
  match goal with
  | [ H: (eval_expr _ _ _ _ _ (Eop _ Enil) _) |- _ ] =>
      inv H; InvEval1
  | [ H: (eval_expr _ _ _ _ _ (Eop _ (_ ::: Enil)) _) |- _ ] =>
      inv H; InvEval1
  | [ H: (eval_expr _ _ _ _ _ (Eop _ (_ ::: _ ::: Enil)) _) |- _ ] =>
      inv H; InvEval1
  | [ H: (eval_exprlist _ _ _ _ _ Enil _) |- _ ] =>
      inv H; InvEval1
  | [ H: (eval_exprlist _ _ _ _ _ (_ ::: _) _) |- _ ] =>
      inv H; InvEval1
  | _ =>
      idtac
  end.

Ltac InvEval2 :=
  match goal with
  | [ H: (eval_operation _ _ _ nil _ = Some _) |- _ ] =>
      simpl in H; inv H
  | [ H: (eval_operation _ _ _ (_ :: nil) _ = Some _) |- _ ] =>
      simpl in H; FuncInv
  | [ H: (eval_operation _ _ _ (_ :: _ :: nil) _ = Some _) |- _ ] =>
      simpl in H; FuncInv
  | [ H: (eval_operation _ _ _ (_ :: _ :: _ :: nil) _ = Some _) |- _ ] =>
      simpl in H; FuncInv
  | _ =>
      idtac
  end.

Ltac InvEval := InvEval1; InvEval2; InvEval2.

(** * Correctness of the smart constructors *)

(** We now show that the code generated by "smart constructor" functions
  such as [Selection.notint] behaves as expected.  Continuing the
  [notint] example, we show that if the expression [e]
  evaluates to some integer value [Vint n], then [Selection.notint e]
  evaluates to a value [Vint (Int.not n)] which is indeed the integer
  negation of the value of [e].

  All proofs follow a common pattern:
- Reasoning by case over the result of the classification functions
  (such as [add_match] for integer addition), gathering additional
  information on the shape of the argument expressions in the non-default
  cases.
- Inversion of the evaluations of the arguments, exploiting the additional
  information thus gathered.
- Equational reasoning over the arithmetic operations performed,
  using the lemmas from the [Int] and [Float] modules.
- Construction of an evaluation derivation for the expression returned
  by the smart constructor.
*)

Theorem eval_notint:
  forall le a x,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le (notint a) (Vint (Int.not x)).
Proof.
  unfold notint; intros until x; case (notint_match a); intros; InvEval.
  EvalOp. simpl. congruence.
  subst x. rewrite Int.not_involutive.  auto.
  EvalOp. simpl. subst x. rewrite Int.not_involutive. auto.
  EvalOp.
Qed.

Lemma eval_notbool_base:
  forall le a v b,
  eval_expr ge sp e m le a v ->
  Val.bool_of_val v b ->
  eval_expr ge sp e m le (notbool_base a) (Val.of_bool (negb b)).
Proof. 
  TrivialOp notbool_base. simpl. 
  inv H0. 
  rewrite Int.eq_false; auto.
  rewrite Int.eq_true; auto.
  reflexivity.
Qed.

Hint Resolve Val.bool_of_true_val Val.bool_of_false_val
             Val.bool_of_true_val_inv Val.bool_of_false_val_inv: valboolof.

Theorem eval_notbool:
  forall le a v b,
  eval_expr ge sp e m le a v ->
  Val.bool_of_val v b ->
  eval_expr ge sp e m le (notbool a) (Val.of_bool (negb b)).
Proof.
  induction a; simpl; intros; try (eapply eval_notbool_base; eauto).
  destruct o; try (eapply eval_notbool_base; eauto).

  destruct e0. InvEval. 
  inv H0. rewrite Int.eq_false; auto. 
  simpl; eauto with evalexpr.
  rewrite Int.eq_true; simpl; eauto with evalexpr.
  eapply eval_notbool_base; eauto.

  inv H. eapply eval_Eop; eauto.
  simpl. assert (eval_condition c vl m = Some b).
  generalize H6. simpl. 
  case (eval_condition c vl m); intros.
  destruct b0; inv H1; inversion H0; auto; congruence.
  congruence.
  rewrite (Op.eval_negate_condition _ _ _ H). 
  destruct b; reflexivity.

  inv H. eapply eval_Econdition; eauto. 
  destruct v1; eauto.
Qed.

Theorem eval_addimm:
  forall le n a x,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le (addimm n a) (Vint (Int.add x n)).
Proof.
  unfold addimm; intros until x.
  generalize (Int.eq_spec n Int.zero). case (Int.eq n Int.zero); intro.
  subst n. rewrite Int.add_zero. auto.
  case (addimm_match a); intros; InvEval; EvalOp; simpl.
  rewrite Int.add_commut. auto.
  destruct (Genv.find_symbol ge s); discriminate.
  destruct sp; simpl in H1; discriminate.
  subst x. rewrite Int.add_assoc. decEq; decEq; decEq. apply Int.add_commut.
Qed. 

Theorem eval_addimm_ptr:
  forall le n a b ofs,
  eval_expr ge sp e m le a (Vptr b ofs) ->
  eval_expr ge sp e m le (addimm n a) (Vptr b (Int.add ofs n)).
Proof.
  unfold addimm; intros until ofs.
  generalize (Int.eq_spec n Int.zero). case (Int.eq n Int.zero); intro.
  subst n. rewrite Int.add_zero. auto.
  case (addimm_match a); intros; InvEval; EvalOp; simpl.
  destruct (Genv.find_symbol ge s). 
  rewrite Int.add_commut. congruence.
  discriminate.
  destruct sp; simpl in H1; try discriminate.
  inv H1. simpl. decEq. decEq. 
  rewrite Int.add_assoc. decEq. apply Int.add_commut.
  subst. rewrite (Int.add_commut n m0). rewrite Int.add_assoc. auto.
Qed.

Theorem eval_add:
  forall le a b x y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  eval_expr ge sp e m le (add a b) (Vint (Int.add x y)).
Proof.
  intros until y.
  unfold add; case (add_match a b); intros; InvEval.
  rewrite Int.add_commut. apply eval_addimm. auto. 
  replace (Int.add x y) with (Int.add (Int.add i0 i) (Int.add n1 n2)).
    apply eval_addimm. EvalOp.  
    subst x; subst y. 
    repeat rewrite Int.add_assoc. decEq. apply Int.add_permut. 
  replace (Int.add x y) with (Int.add (Int.add i y) n1).
    apply eval_addimm. EvalOp.
    subst x. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  apply eval_addimm. auto.
  replace (Int.add x y) with (Int.add (Int.add x i) n2).
    apply eval_addimm. EvalOp.
    subst y. rewrite Int.add_assoc. auto.
  EvalOp. simpl. subst x. rewrite Int.add_commut. auto.
  EvalOp. simpl. congruence.
  EvalOp.
Qed.

Theorem eval_add_ptr:
  forall le a b p x y,
  eval_expr ge sp e m le a (Vptr p x) ->
  eval_expr ge sp e m le b (Vint y) ->
  eval_expr ge sp e m le (add a b) (Vptr p (Int.add x y)).
Proof.
  intros until y. unfold add; case (add_match a b); intros; InvEval.
  replace (Int.add x y) with (Int.add (Int.add i0 i) (Int.add n1 n2)).
    apply eval_addimm_ptr. subst b0. EvalOp. 
    subst x; subst y.
    repeat rewrite Int.add_assoc. decEq. apply Int.add_permut. 
  replace (Int.add x y) with (Int.add (Int.add i y) n1).
    apply eval_addimm_ptr. subst b0. EvalOp.
    subst x. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  apply eval_addimm_ptr. auto.
  replace (Int.add x y) with (Int.add (Int.add x i) n2).
    apply eval_addimm_ptr. EvalOp.
    subst y. rewrite Int.add_assoc. auto.
  EvalOp. simpl. congruence.
  EvalOp.
Qed.

Theorem eval_add_ptr_2:
  forall le a b x p y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vptr p y) ->
  eval_expr ge sp e m le (add a b) (Vptr p (Int.add y x)).
Proof.
  intros until y. unfold add; case (add_match a b); intros; InvEval.
  apply eval_addimm_ptr. auto.
  replace (Int.add y x) with (Int.add (Int.add i i0) (Int.add n1 n2)).
    apply eval_addimm_ptr. subst b0. EvalOp. 
    subst x; subst y.
    repeat rewrite Int.add_assoc. decEq. 
    rewrite (Int.add_commut n1 n2). apply Int.add_permut. 
  replace (Int.add y x) with (Int.add (Int.add y i) n1).
    apply eval_addimm_ptr. EvalOp. 
    subst x. repeat rewrite Int.add_assoc. auto.
  replace (Int.add y x) with (Int.add (Int.add i x) n2).
    apply eval_addimm_ptr. EvalOp. subst b0; reflexivity.
    subst y. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  EvalOp. simpl. congruence.
  EvalOp.
Qed.

Theorem eval_sub:
  forall le a b x y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  eval_expr ge sp e m le (sub a b) (Vint (Int.sub x y)).
Proof.
  intros until y.
  unfold sub; case (sub_match a b); intros; InvEval.
  rewrite Int.sub_add_opp. 
    apply eval_addimm. assumption.
  replace (Int.sub x y) with (Int.add (Int.sub i0 i) (Int.sub n1 n2)).
    apply eval_addimm. EvalOp.
    subst x; subst y.
    repeat rewrite Int.sub_add_opp.
    repeat rewrite Int.add_assoc. decEq. 
    rewrite Int.add_permut. decEq. symmetry. apply Int.neg_add_distr.
  replace (Int.sub x y) with (Int.add (Int.sub i y) n1).
    apply eval_addimm. EvalOp.
    subst x. rewrite Int.sub_add_l. auto.
  replace (Int.sub x y) with (Int.add (Int.sub x i) (Int.neg n2)).
    apply eval_addimm. EvalOp.
    subst y. rewrite (Int.add_commut i n2). symmetry. apply Int.sub_add_r.
  EvalOp. 
  EvalOp. simpl. congruence.
  EvalOp. simpl. congruence.
  EvalOp.
Qed.

Theorem eval_sub_ptr_int:
  forall le a b p x y,
  eval_expr ge sp e m le a (Vptr p x) ->
  eval_expr ge sp e m le b (Vint y) ->
  eval_expr ge sp e m le (sub a b) (Vptr p (Int.sub x y)).
Proof.
  intros until y.
  unfold sub; case (sub_match a b); intros; InvEval.
  rewrite Int.sub_add_opp. 
    apply eval_addimm_ptr. assumption.
  subst b0. replace (Int.sub x y) with (Int.add (Int.sub i0 i) (Int.sub n1 n2)).
    apply eval_addimm_ptr. EvalOp.
    subst x; subst y.
    repeat rewrite Int.sub_add_opp.
    repeat rewrite Int.add_assoc. decEq. 
    rewrite Int.add_permut. decEq. symmetry. apply Int.neg_add_distr.
  subst b0. replace (Int.sub x y) with (Int.add (Int.sub i y) n1).
    apply eval_addimm_ptr. EvalOp.
    subst x. rewrite Int.sub_add_l. auto.
  replace (Int.sub x y) with (Int.add (Int.sub x i) (Int.neg n2)).
    apply eval_addimm_ptr. EvalOp.
    subst y. rewrite (Int.add_commut i n2). symmetry. apply Int.sub_add_r.
  EvalOp. simpl. congruence.  
  EvalOp.
Qed.

Theorem eval_sub_ptr_ptr:
  forall le a b p x y,
  eval_expr ge sp e m le a (Vptr p x) ->
  eval_expr ge sp e m le b (Vptr p y) ->
  eval_expr ge sp e m le (sub a b) (Vint (Int.sub x y)).
Proof.
  intros until y.
  unfold sub; case (sub_match a b); intros; InvEval.
  replace (Int.sub x y) with (Int.add (Int.sub i0 i) (Int.sub n1 n2)).
    apply eval_addimm. EvalOp. 
    simpl; unfold eq_block. subst b0; subst b1; rewrite zeq_true. auto.
    subst x; subst y.
    repeat rewrite Int.sub_add_opp.
    repeat rewrite Int.add_assoc. decEq. 
    rewrite Int.add_permut. decEq. symmetry. apply Int.neg_add_distr.
  subst b0. replace (Int.sub x y) with (Int.add (Int.sub i y) n1).
    apply eval_addimm. EvalOp.
    simpl. unfold eq_block. rewrite zeq_true. auto.
    subst x. rewrite Int.sub_add_l. auto.
  subst b0. replace (Int.sub x y) with (Int.add (Int.sub x i) (Int.neg n2)).
    apply eval_addimm. EvalOp.
    simpl. unfold eq_block. rewrite zeq_true. auto.
    subst y. rewrite (Int.add_commut i n2). symmetry. apply Int.sub_add_r. 
  EvalOp. simpl. unfold eq_block. rewrite zeq_true. auto.
Qed.

Theorem eval_shlimm:
  forall le a n x,
  eval_expr ge sp e m le a (Vint x) ->
  Int.ltu n (Int.repr 32) = true ->
  eval_expr ge sp e m le (shlimm a n) (Vint (Int.shl x n)).
Proof.
  intros until x.  unfold shlimm, is_shift_amount.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intro.
  intros. subst n. rewrite Int.shl_zero. auto.
  destruct (is_shift_amount_aux n). simpl. 
  case (shlimm_match a); intros; InvEval.
  EvalOp.
  destruct (is_shift_amount_aux (Int.add n (s_amount n1))).
  EvalOp. simpl. subst x.
  decEq. decEq. symmetry. rewrite Int.add_commut. apply Int.shl_shl.
  apply s_amount_ltu. auto.
  rewrite Int.add_commut. auto.
  EvalOp. econstructor. EvalOp. simpl. reflexivity. constructor.
  simpl. congruence.
  EvalOp.
  congruence. 
Qed.

Theorem eval_shruimm:
  forall le a n x,
  eval_expr ge sp e m le a (Vint x) ->
  Int.ltu n (Int.repr 32) = true ->
  eval_expr ge sp e m le (shruimm a n) (Vint (Int.shru x n)).
Proof.
  intros until x.  unfold shruimm, is_shift_amount.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intro.
  intros. subst n. rewrite Int.shru_zero. auto.
  destruct (is_shift_amount_aux n). simpl. 
  case (shruimm_match a); intros; InvEval.
  EvalOp.
  destruct (is_shift_amount_aux (Int.add n (s_amount n1))).
  EvalOp. simpl. subst x.
  decEq. decEq. symmetry. rewrite Int.add_commut. apply Int.shru_shru.
  apply s_amount_ltu. auto.
  rewrite Int.add_commut. auto.
  EvalOp. econstructor. EvalOp. simpl. reflexivity. constructor.
  simpl. congruence.
  EvalOp.
  congruence. 
Qed.

Theorem eval_shrimm:
  forall le a n x,
  eval_expr ge sp e m le a (Vint x) ->
  Int.ltu n (Int.repr 32) = true ->
  eval_expr ge sp e m le (shrimm a n) (Vint (Int.shr x n)).
Proof.
  intros until x.  unfold shrimm, is_shift_amount.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intro.
  intros. subst n. rewrite Int.shr_zero. auto.
  destruct (is_shift_amount_aux n). simpl. 
  case (shrimm_match a); intros; InvEval.
  EvalOp.
  destruct (is_shift_amount_aux (Int.add n (s_amount n1))).
  EvalOp. simpl. subst x.
  decEq. decEq. symmetry. rewrite Int.add_commut. apply Int.shr_shr.
  apply s_amount_ltu. auto.
  rewrite Int.add_commut. auto.
  EvalOp. econstructor. EvalOp. simpl. reflexivity. constructor.
  simpl. congruence.
  EvalOp.
  congruence. 
Qed.

Lemma eval_mulimm_base:
  forall le a n x,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le (mulimm_base n a) (Vint (Int.mul x n)).
Proof.
  intros; unfold mulimm_base. 
  generalize (Int.one_bits_decomp n). 
  generalize (Int.one_bits_range n).
  change (Z_of_nat wordsize) with 32.
  destruct (Int.one_bits n).
  intros. EvalOp. constructor. EvalOp. simpl; reflexivity.
  constructor. eauto. constructor. simpl. rewrite Int.mul_commut. auto.
  destruct l.
  intros. rewrite H1. simpl. 
  rewrite Int.add_zero. rewrite <- Int.shl_mul.
  apply eval_shlimm. auto. auto with coqlib. 
  destruct l.
  intros. apply eval_Elet with (Vint x). auto.
  rewrite H1. simpl. rewrite Int.add_zero. 
  rewrite Int.mul_add_distr_r.
  rewrite <- Int.shl_mul.
  rewrite <- Int.shl_mul.
  apply eval_add. 
  apply eval_shlimm. apply eval_Eletvar. simpl. reflexivity. 
  auto with coqlib.
  apply eval_shlimm. apply eval_Eletvar. simpl. reflexivity.
  auto with coqlib.
  intros. EvalOp. constructor. EvalOp. simpl; reflexivity. 
  constructor. eauto. constructor. simpl. rewrite Int.mul_commut. auto.
Qed.

Theorem eval_mulimm:
  forall le a n x,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le (mulimm n a) (Vint (Int.mul x n)).
Proof.
  intros until x; unfold mulimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intro.
  subst n. rewrite Int.mul_zero. 
  intro. EvalOp. 
  generalize (Int.eq_spec n Int.one); case (Int.eq n Int.one); intro.
  subst n. rewrite Int.mul_one. auto.
  case (mulimm_match a); intros; InvEval.
  EvalOp. rewrite Int.mul_commut. reflexivity.
  replace (Int.mul x n) with (Int.add (Int.mul i n) (Int.mul n n2)).
  apply eval_addimm. apply eval_mulimm_base. auto.
  subst x. rewrite Int.mul_add_distr_l. decEq. apply Int.mul_commut.
  apply eval_mulimm_base. assumption.
Qed.

Theorem eval_mul:
  forall le a b x y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  eval_expr ge sp e m le (mul a b) (Vint (Int.mul x y)).
Proof.
  intros until y.
  unfold mul; case (mul_match a b); intros; InvEval.
  rewrite Int.mul_commut. apply eval_mulimm. auto. 
  apply eval_mulimm. auto.
  EvalOp.
Qed.

Theorem eval_divs_base:
  forall le a b x y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  y <> Int.zero ->
  eval_expr ge sp e m le (Eop Odiv (a ::: b ::: Enil)) (Vint (Int.divs x y)).
Proof.
  intros. EvalOp; simpl.
  predSpec Int.eq Int.eq_spec y Int.zero. contradiction. auto.
Qed.

Theorem eval_divs:
  forall le a x b y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  y <> Int.zero ->
  eval_expr ge sp e m le (divs a b) (Vint (Int.divs x y)).
Proof.
  intros until y.
  unfold divs; case (divu_match b); intros; InvEval.
  caseEq (Int.is_power2 y); intros.
  caseEq (Int.ltu i (Int.repr 31)); intros.
  EvalOp. simpl. unfold Int.ltu. rewrite zlt_true. 
  rewrite (Int.divs_pow2 x y i H0). auto.
  exploit Int.ltu_inv; eauto. 
  change (Int.unsigned (Int.repr 31)) with 31.
  change (Int.unsigned (Int.repr 32)) with 32.
  omega.
  apply eval_divs_base. auto. EvalOp. auto.
  apply eval_divs_base. auto. EvalOp. auto.
  apply eval_divs_base; auto. 
Qed.

Lemma eval_mod_aux:
  forall divop semdivop,
  (forall sp x y m,
   y <> Int.zero ->
   eval_operation ge sp divop (Vint x :: Vint y :: nil) m =
   Some (Vint (semdivop x y))) ->
  forall le a b x y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  y <> Int.zero ->
  eval_expr ge sp e m le (mod_aux divop a b)
   (Vint (Int.sub x (Int.mul (semdivop x y) y))).
Proof.
  intros; unfold mod_aux.
  eapply eval_Elet. eexact H0. eapply eval_Elet. 
  apply eval_lift. eexact H1.
  eapply eval_Eop. eapply eval_Econs. 
  eapply eval_Eletvar. simpl; reflexivity.
  eapply eval_Econs. eapply eval_Eop. 
  eapply eval_Econs. eapply eval_Eop.
  eapply eval_Econs. apply eval_Eletvar. simpl; reflexivity.
  eapply eval_Econs. apply eval_Eletvar. simpl; reflexivity.
  apply eval_Enil.  
  apply H. assumption.
  eapply eval_Econs. apply eval_Eletvar. simpl; reflexivity.
  apply eval_Enil.  
  simpl; reflexivity. apply eval_Enil. 
  reflexivity.
Qed.

Theorem eval_mods:
  forall le a b x y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  y <> Int.zero ->
  eval_expr ge sp e m le (mods a b) (Vint (Int.mods x y)).
Proof.
  intros; unfold mods. 
  rewrite Int.mods_divs. 
  eapply eval_mod_aux; eauto. 
  intros. simpl. predSpec Int.eq Int.eq_spec y0 Int.zero. 
  contradiction. auto.
Qed.

Lemma eval_divu_base:
  forall le a x b y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  y <> Int.zero ->
  eval_expr ge sp e m le (Eop Odivu (a ::: b ::: Enil)) (Vint (Int.divu x y)).
Proof.
  intros. EvalOp. simpl. 
  predSpec Int.eq Int.eq_spec y Int.zero. contradiction. auto.
Qed.

Theorem eval_divu:
  forall le a x b y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  y <> Int.zero ->
  eval_expr ge sp e m le (divu a b) (Vint (Int.divu x y)).
Proof.
  intros until y.
  unfold divu; case (divu_match b); intros; InvEval.
  caseEq (Int.is_power2 y). 
  intros. rewrite (Int.divu_pow2 x y i H0).
  apply eval_shruimm. auto.
  apply Int.is_power2_range with y. auto.
  intros. apply eval_divu_base. auto. EvalOp. auto.
  eapply eval_divu_base; eauto.
Qed.

Theorem eval_modu:
  forall le a x b y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  y <> Int.zero ->
  eval_expr ge sp e m le (modu a b) (Vint (Int.modu x y)).
Proof.
  intros until y; unfold modu; case (divu_match b); intros; InvEval.
  caseEq (Int.is_power2 y). 
  intros. rewrite (Int.modu_and x y i H0).
  EvalOp. 
  intro. rewrite Int.modu_divu. eapply eval_mod_aux. 
  intros. simpl. predSpec Int.eq Int.eq_spec y0 Int.zero.
  contradiction. auto.
  auto. EvalOp. auto. auto.
  rewrite Int.modu_divu. eapply eval_mod_aux. 
  intros. simpl. predSpec Int.eq Int.eq_spec y0 Int.zero.
  contradiction. auto. auto. auto. auto. auto.
Qed.

Theorem eval_and:
  forall le a x b y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  eval_expr ge sp e m le (and a b) (Vint (Int.and x y)).
Proof.
  intros until y; unfold and; case (and_match a b); intros; InvEval.
  rewrite Int.and_commut. EvalOp. simpl. congruence.
  EvalOp. simpl. congruence.
  rewrite Int.and_commut. EvalOp. simpl. congruence.
  EvalOp. simpl. congruence.
  rewrite Int.and_commut. EvalOp. simpl. congruence.
  EvalOp. simpl. congruence.
  EvalOp.
Qed.

Remark eval_same_expr:
  forall a1 a2 le v1 v2,
  same_expr_pure a1 a2 = true ->
  eval_expr ge sp e m le a1 v1 ->
  eval_expr ge sp e m le a2 v2 ->
  a1 = a2 /\ v1 = v2.
Proof.
  intros until v2.
  destruct a1; simpl; try (intros; discriminate). 
  destruct a2; simpl; try (intros; discriminate).
  case (ident_eq i i0); intros.
  subst i0. inversion H0. inversion H1. split. auto. congruence. 
  discriminate.
Qed.

Lemma eval_or:
  forall le a x b y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  eval_expr ge sp e m le (or a b) (Vint (Int.or x y)).
Proof.
  intros until y; unfold or; case (or_match a b); intros; InvEval.
  caseEq (Int.eq (Int.add (s_amount n1) (s_amount n2)) (Int.repr 32)
          && same_expr_pure t1 t2); intro.
  destruct (andb_prop _ _ H1).
  generalize (Int.eq_spec (Int.add (s_amount n1) (s_amount n2)) (Int.repr 32)).
  rewrite H4. intro. 
  exploit eval_same_expr; eauto. intros [EQ1 EQ2]. inv EQ1. inv EQ2. 
  simpl. EvalOp. simpl. decEq. decEq. apply Int.or_ror.
  destruct n1; auto. destruct n2; auto. auto. 
  EvalOp. econstructor. EvalOp. simpl. reflexivity.
  econstructor; eauto with evalexpr. 
  simpl. congruence. 
  EvalOp. simpl. rewrite Int.or_commut. congruence.
  EvalOp. simpl. congruence.
  EvalOp. 
Qed.

Theorem eval_xor:
  forall le a x b y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  eval_expr ge sp e m le (xor a b) (Vint (Int.xor x y)).
Proof.
  intros until y; unfold xor; case (xor_match a b); intros; InvEval.
  rewrite Int.xor_commut. EvalOp. simpl. congruence.
  EvalOp. simpl. congruence.
  EvalOp.
Qed.

Theorem eval_shl:
  forall le a x b y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  Int.ltu y (Int.repr 32) = true ->
  eval_expr ge sp e m le (shl a b) (Vint (Int.shl x y)).
Proof.
  intros until y; unfold shl; case (shift_match b); intros.
  InvEval. apply eval_shlimm; auto.
  EvalOp. simpl. rewrite H1. auto.
Qed.

Theorem eval_shru:
  forall le a x b y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  Int.ltu y (Int.repr 32) = true ->
  eval_expr ge sp e m le (shru a b) (Vint (Int.shru x y)).
Proof.
  intros until y; unfold shru; case (shift_match b); intros.
  InvEval. apply eval_shruimm; auto.
  EvalOp. simpl. rewrite H1. auto.
Qed.

Theorem eval_shr:
  forall le a x b y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  Int.ltu y (Int.repr 32) = true ->
  eval_expr ge sp e m le (shr a b) (Vint (Int.shr x y)).
Proof.
  intros until y; unfold shr; case (shift_match b); intros.
  InvEval. apply eval_shrimm; auto.
  EvalOp. simpl. rewrite H1. auto.
Qed.

Theorem eval_cast8signed:
  forall le a v,
  eval_expr ge sp e m le a v ->
  eval_expr ge sp e m le (cast8signed a) (Val.sign_ext 8 v).
Proof. 
  intros until v; unfold cast8signed; case (cast8signed_match a); intros; InvEval.
  EvalOp. simpl. subst v. destruct v1; simpl; auto.
  rewrite Int.sign_ext_idem. reflexivity. vm_compute; auto.
  EvalOp.
Qed.

Theorem eval_cast8unsigned:
  forall le a v,
  eval_expr ge sp e m le a v ->
  eval_expr ge sp e m le (cast8unsigned a) (Val.zero_ext 8 v).
Proof. 
  intros until v; unfold cast8unsigned; case (cast8unsigned_match a); intros; InvEval.
  EvalOp. simpl. subst v. destruct v1; simpl; auto.
  rewrite Int.zero_ext_idem. reflexivity. vm_compute; auto.
  EvalOp.
Qed.

Theorem eval_cast16signed:
  forall le a v,
  eval_expr ge sp e m le a v ->
  eval_expr ge sp e m le (cast16signed a) (Val.sign_ext 16 v).
Proof. 
  intros until v; unfold cast16signed; case (cast16signed_match a); intros; InvEval.
  EvalOp. simpl. subst v. destruct v1; simpl; auto.
  rewrite Int.sign_ext_idem. reflexivity. vm_compute; auto.
  EvalOp.
Qed.

Theorem eval_cast16unsigned:
  forall le a v,
  eval_expr ge sp e m le a v ->
  eval_expr ge sp e m le (cast16unsigned a) (Val.zero_ext 16 v).
Proof. 
  intros until v; unfold cast16unsigned; case (cast16unsigned_match a); intros; InvEval.
  EvalOp. simpl. subst v. destruct v1; simpl; auto.
  rewrite Int.zero_ext_idem. reflexivity. vm_compute; auto.
  EvalOp.
Qed.

Theorem eval_singleoffloat:
  forall le a v,
  eval_expr ge sp e m le a v ->
  eval_expr ge sp e m le (singleoffloat a) (Val.singleoffloat v).
Proof. 
  intros until v; unfold singleoffloat; case (singleoffloat_match a); intros; InvEval.
  EvalOp. simpl. subst v. destruct v1; simpl; auto. rewrite Float.singleoffloat_idem. reflexivity.
  EvalOp.
Qed.

Theorem eval_comp_int:
  forall le c a x b y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  eval_expr ge sp e m le (comp c a b) (Val.of_bool(Int.cmp c x y)).
Proof.
  intros until y.
  unfold comp; case (comp_match a b); intros; InvEval.
  EvalOp. simpl. rewrite Int.swap_cmp. destruct (Int.cmp c x y); reflexivity.
  EvalOp. simpl. destruct (Int.cmp c x y); reflexivity.
  EvalOp. simpl. rewrite Int.swap_cmp. rewrite H. destruct (Int.cmp c x y); reflexivity.
  EvalOp. simpl. rewrite H0. destruct (Int.cmp c x y); reflexivity.
  EvalOp. simpl. destruct (Int.cmp c x y); reflexivity.
Qed.

Remark eval_compare_null_trans:
  forall c x v,
  (if Int.eq x Int.zero then Cminor.eval_compare_mismatch c else None) = Some v ->
  match eval_compare_null c x with
  | Some true => Some Vtrue
  | Some false => Some Vfalse
  | None => None (A:=val)
  end = Some v.
Proof.
  unfold Cminor.eval_compare_mismatch, eval_compare_null; intros.
  destruct (Int.eq x Int.zero); try discriminate. 
  destruct c; try discriminate; auto.
Qed.

Theorem eval_comp_ptr_int:
  forall le c a x1 x2 b y v,
  eval_expr ge sp e m le a (Vptr x1 x2) ->
  eval_expr ge sp e m le b (Vint y) ->
  (if Int.eq y Int.zero then Cminor.eval_compare_mismatch c else None) = Some v ->
  eval_expr ge sp e m le (comp c a b) v.
Proof.
  intros until v.
  unfold comp; case (comp_match a b); intros; InvEval.
  EvalOp. simpl. apply eval_compare_null_trans; auto. 
  EvalOp. simpl. rewrite H0. apply eval_compare_null_trans; auto. 
  EvalOp. simpl. apply eval_compare_null_trans; auto.
Qed.

Remark eval_swap_compare_null_trans:
  forall c x v,
  (if Int.eq x Int.zero then Cminor.eval_compare_mismatch c else None) = Some v ->
  match eval_compare_null (swap_comparison c) x with
  | Some true => Some Vtrue
  | Some false => Some Vfalse
  | None => None (A:=val)
  end = Some v.
Proof.
  unfold Cminor.eval_compare_mismatch, eval_compare_null; intros.
  destruct (Int.eq x Int.zero); try discriminate. 
  destruct c; simpl; try discriminate; auto.
Qed.

Theorem eval_comp_int_ptr:
  forall le c a x b y1 y2 v,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vptr y1 y2) ->
  (if Int.eq x Int.zero then Cminor.eval_compare_mismatch c else None) = Some v ->
  eval_expr ge sp e m le (comp c a b) v.
Proof.
  intros until v.
  unfold comp; case (comp_match a b); intros; InvEval.
  EvalOp. simpl. apply eval_swap_compare_null_trans; auto. 
  EvalOp. simpl. rewrite H. apply eval_swap_compare_null_trans; auto. 
  EvalOp. simpl. apply eval_compare_null_trans; auto.
Qed.

Theorem eval_comp_ptr_ptr:
  forall le c a x1 x2 b y1 y2,
  eval_expr ge sp e m le a (Vptr x1 x2) ->
  eval_expr ge sp e m le b (Vptr y1 y2) ->
  valid_pointer m x1 (Int.signed x2) &&
  valid_pointer m y1 (Int.signed y2) = true ->
  x1 = y1 ->
  eval_expr ge sp e m le (comp c a b) (Val.of_bool(Int.cmp c x2 y2)).
Proof.
  intros until y2.
  unfold comp; case (comp_match a b); intros; InvEval.
  EvalOp. simpl. rewrite H1. simpl. 
  subst y1. rewrite dec_eq_true. 
  destruct (Int.cmp c x2 y2); reflexivity.
Qed.

Theorem eval_comp_ptr_ptr_2:
  forall le c a x1 x2 b y1 y2 v,
  eval_expr ge sp e m le a (Vptr x1 x2) ->
  eval_expr ge sp e m le b (Vptr y1 y2) ->
  valid_pointer m x1 (Int.signed x2) &&
  valid_pointer m y1 (Int.signed y2) = true ->
  x1 <> y1 ->
  Cminor.eval_compare_mismatch c = Some v ->
  eval_expr ge sp e m le (comp c a b) v.
Proof.
  intros until y2.
  unfold comp; case (comp_match a b); intros; InvEval.
  EvalOp. simpl. rewrite H1. rewrite dec_eq_false; auto.
  destruct c; simpl in H3; inv H3; auto.
Qed.


Theorem eval_compu:
  forall le c a x b y,
  eval_expr ge sp e m le a (Vint x) ->
  eval_expr ge sp e m le b (Vint y) ->
  eval_expr ge sp e m le (compu c a b) (Val.of_bool(Int.cmpu c x y)).
Proof.
  intros until y.
  unfold compu; case (comp_match a b); intros; InvEval.
  EvalOp. simpl. rewrite Int.swap_cmpu. destruct (Int.cmpu c x y); reflexivity.
  EvalOp. simpl. destruct (Int.cmpu c x y); reflexivity.
  EvalOp. simpl. rewrite H. rewrite Int.swap_cmpu. destruct (Int.cmpu c x y); reflexivity.
  EvalOp. simpl. rewrite H0. destruct (Int.cmpu c x y); reflexivity.
  EvalOp. simpl. destruct (Int.cmpu c x y); reflexivity.
Qed.

Theorem eval_compf:
  forall le c a x b y,
  eval_expr ge sp e m le a (Vfloat x) ->
  eval_expr ge sp e m le b (Vfloat y) ->
  eval_expr ge sp e m le (compf c a b) (Val.of_bool(Float.cmp c x y)).
Proof.
  intros. unfold compf. EvalOp. simpl. 
  destruct (Float.cmp c x y); reflexivity.
Qed.

Lemma negate_condexpr_correct:
  forall le a b,
  eval_condexpr ge sp e m le a b ->
  eval_condexpr ge sp e m le (negate_condexpr a) (negb b).
Proof.
  induction 1; simpl.
  constructor.
  constructor.
  econstructor. eauto. apply eval_negate_condition. auto.
  econstructor. eauto. destruct vb1; auto.
Qed. 

Scheme expr_ind2 := Induction for expr Sort Prop
  with exprlist_ind2 := Induction for exprlist Sort Prop.

Fixpoint forall_exprlist (P: expr -> Prop) (el: exprlist) {struct el}: Prop :=
  match el with
  | Enil => True
  | Econs e el' => P e /\ forall_exprlist P el'
  end.

Lemma expr_induction_principle:
  forall (P: expr -> Prop),
  (forall i : ident, P (Evar i)) ->
  (forall (o : operation) (e : exprlist),
     forall_exprlist P e -> P (Eop o e)) ->
  (forall (m : memory_chunk) (a : Op.addressing) (e : exprlist),
     forall_exprlist P e -> P (Eload m a e)) ->
  (forall (c : condexpr) (e : expr),
     P e -> forall e0 : expr, P e0 -> P (Econdition c e e0)) ->
  (forall e : expr, P e -> forall e0 : expr, P e0 -> P (Elet e e0)) ->
  (forall n : nat, P (Eletvar n)) ->
  forall e : expr, P e.
Proof.
  intros. apply expr_ind2 with (P := P) (P0 := forall_exprlist P); auto.
  simpl. auto.
  intros. simpl. auto.
Qed.

Lemma eval_base_condition_of_expr:
  forall le a v b,
  eval_expr ge sp e m le a v ->
  Val.bool_of_val v b ->
  eval_condexpr ge sp e m le 
                (CEcond (Ccompimm Cne Int.zero) (a ::: Enil))
                b.
Proof.
  intros. 
  eapply eval_CEcond. eauto with evalexpr. 
  inversion H0; simpl. rewrite Int.eq_false; auto. auto. auto.
Qed.

Lemma is_compare_neq_zero_correct:
  forall c v b,
  is_compare_neq_zero c = true ->
  eval_condition c (v :: nil) m = Some b ->
  Val.bool_of_val v b.
Proof.
  intros.
  destruct c; simpl in H; try discriminate;
  destruct c; simpl in H; try discriminate;
  generalize (Int.eq_spec i Int.zero); rewrite H; intro; subst i.

  simpl in H0. destruct v; inv H0. 
  generalize (Int.eq_spec i Int.zero). destruct (Int.eq i Int.zero); intros; simpl.
  subst i; constructor. constructor; auto. constructor.

  simpl in H0. destruct v; inv H0. 
  generalize (Int.eq_spec i Int.zero). destruct (Int.eq i Int.zero); intros; simpl.
  subst i; constructor. constructor; auto.
Qed.

Lemma is_compare_eq_zero_correct:
  forall c v b,
  is_compare_eq_zero c = true ->
  eval_condition c (v :: nil) m = Some b ->
  Val.bool_of_val v (negb b).
Proof.
  intros. apply is_compare_neq_zero_correct with (negate_condition c).
  destruct c; simpl in H; simpl; try discriminate;
  destruct c; simpl; try discriminate; auto.
  apply eval_negate_condition; auto.
Qed.

Lemma eval_condition_of_expr:
  forall a le v b,
  eval_expr ge sp e m le a v ->
  Val.bool_of_val v b ->
  eval_condexpr ge sp e m le (condexpr_of_expr a) b.
Proof.
  intro a0; pattern a0.
  apply expr_induction_principle; simpl; intros;
    try (eapply eval_base_condition_of_expr; eauto; fail).
  
  destruct o; try (eapply eval_base_condition_of_expr; eauto; fail).

  destruct e0. InvEval. 
  inversion H1. 
  rewrite Int.eq_false; auto. constructor.
  subst i; rewrite Int.eq_true. constructor.
  eapply eval_base_condition_of_expr; eauto.

  inv H0. simpl in H7.
  assert (eval_condition c vl m = Some b).
    destruct (eval_condition c vl m); try discriminate.
    destruct b0; inv H7; inversion H1; congruence.
  assert (eval_condexpr ge sp e m le (CEcond c e0) b).
    eapply eval_CEcond; eauto.
  destruct e0; auto. destruct e1; auto.
  simpl in H. destruct H.
  inv H5. inv H11.

  case_eq (is_compare_neq_zero c); intros.
  eapply H; eauto.
  apply is_compare_neq_zero_correct with c; auto.

  case_eq (is_compare_eq_zero c); intros.
  replace b with (negb (negb b)). apply negate_condexpr_correct.
  eapply H; eauto.
  apply is_compare_eq_zero_correct with c; auto.
  apply negb_involutive.

  auto.

  inv H1. destruct v1; eauto with evalexpr.
Qed.

Lemma eval_addressing:
  forall le chunk a v b ofs,
  eval_expr ge sp e m le a v ->
  v = Vptr b ofs ->
  match addressing chunk a with (mode, args) =>
    exists vl,
    eval_exprlist ge sp e m le args vl /\ 
    eval_addressing ge sp mode vl = Some v
  end.
Proof.
  intros until v. unfold addressing; case (addressing_match a); intros; InvEval.
  exists (@nil val). split. eauto with evalexpr. simpl. auto.
  exists (Vptr b0 i :: nil). split. eauto with evalexpr. 
    simpl. congruence.
  destruct (is_float_addressing chunk).
  exists (Vptr b0 ofs :: nil).
    split. constructor. econstructor. eauto with evalexpr. simpl. congruence. constructor. 
    simpl. rewrite Int.add_zero. congruence.
  exists (Vptr b0 i :: Vint i0 :: nil).
    split. eauto with evalexpr. simpl. congruence.
  destruct (is_float_addressing chunk).
  exists (Vptr b0 ofs :: nil).
    split. constructor. econstructor. eauto with evalexpr. simpl. congruence. constructor. 
    simpl. rewrite Int.add_zero. congruence.
  exists (Vint i :: Vptr b0 i0 :: nil).
    split. eauto with evalexpr. simpl. 
    rewrite Int.add_commut. congruence.
  destruct (is_float_addressing chunk).
  exists (Vptr b0 ofs :: nil).
    split. constructor. econstructor. eauto with evalexpr. simpl. congruence. constructor. 
    simpl. rewrite Int.add_zero. congruence.
  exists (Vptr b0 i :: Vint i0 :: nil).
    split. eauto with evalexpr. simpl. congruence.
  exists (v :: nil). split. eauto with evalexpr. 
    subst v. simpl. rewrite Int.add_zero. auto.
Qed.

Lemma eval_load:
  forall le a v chunk v',
  eval_expr ge sp e m le a v ->
  Mem.loadv chunk m v = Some v' ->
  eval_expr ge sp e m le (load chunk a) v'.
Proof.
  intros. generalize H0; destruct v; simpl; intro; try discriminate.
  unfold load. 
  generalize (eval_addressing _ chunk _ _ _ _ H (refl_equal _)).
  destruct (addressing chunk a). intros [vl [EV EQ]]. 
  eapply eval_Eload; eauto. 
Qed.

Lemma eval_store:
  forall chunk a1 a2 v1 v2 f k m',
  eval_expr ge sp e m nil a1 v1 ->
  eval_expr ge sp e m nil a2 v2 ->
  Mem.storev chunk m v1 v2 = Some m' ->
  step ge (State f (store chunk a1 a2) k sp e m)
       E0 (State f Sskip k sp e m').
Proof.
  intros. generalize H1; destruct v1; simpl; intro; try discriminate.
  unfold store.
  generalize (eval_addressing _ chunk _ _ _ _ H (refl_equal _)).
  destruct (addressing chunk a1). intros [vl [EV EQ]]. 
  eapply step_store; eauto. 
Qed.

(** * Correctness of instruction selection for operators *)

(** We now prove a semantic preservation result for the [sel_unop]
  and [sel_binop] selection functions.  The proof exploits
  the results of the previous section. *)

Lemma eval_sel_unop:
  forall le op a1 v1 v,
  eval_expr ge sp e m le a1 v1 ->
  eval_unop op v1 = Some v ->
  eval_expr ge sp e m le (sel_unop op a1) v.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_cast8unsigned; auto.
  apply eval_cast8signed; auto.
  apply eval_cast16unsigned; auto.
  apply eval_cast16signed; auto.
  EvalOp. 
  generalize (Int.eq_spec i Int.zero). destruct (Int.eq i Int.zero); intro.
  change true with (negb false). eapply eval_notbool; eauto. subst i; constructor.
  change false with (negb true). eapply eval_notbool; eauto. constructor; auto.
  change Vfalse with (Val.of_bool (negb true)).
  eapply eval_notbool; eauto. constructor.
  apply eval_notint; auto.
  EvalOp.
  EvalOp.
  apply eval_singleoffloat; auto.
  EvalOp.
  EvalOp.
  EvalOp.
  EvalOp.
Qed.

Lemma eval_sel_binop:
  forall le op a1 a2 v1 v2 v,
  eval_expr ge sp e m le a1 v1 ->
  eval_expr ge sp e m le a2 v2 ->
  eval_binop op v1 v2 m = Some v ->
  eval_expr ge sp e m le (sel_binop op a1 a2) v.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_add; auto.
  apply eval_add_ptr_2; auto.
  apply eval_add_ptr; auto.
  apply eval_sub; auto.
  apply eval_sub_ptr_int; auto.
  destruct (eq_block b b0); inv H1. 
  eapply eval_sub_ptr_ptr; eauto.
  apply eval_mul; eauto.
  generalize (Int.eq_spec i0 Int.zero). destruct (Int.eq i0 Int.zero); inv H1.
  apply eval_divs; eauto.
  generalize (Int.eq_spec i0 Int.zero). destruct (Int.eq i0 Int.zero); inv H1.
  apply eval_divu; eauto.
  generalize (Int.eq_spec i0 Int.zero). destruct (Int.eq i0 Int.zero); inv H1.
  apply eval_mods; eauto.
  generalize (Int.eq_spec i0 Int.zero). destruct (Int.eq i0 Int.zero); inv H1.
  apply eval_modu; eauto.
  apply eval_and; auto.
  apply eval_or; auto.
  apply eval_xor; auto.
  caseEq (Int.ltu i0 (Int.repr 32)); intro; rewrite H2 in H1; inv H1.
  apply eval_shl; auto.
  caseEq (Int.ltu i0 (Int.repr 32)); intro; rewrite H2 in H1; inv H1.
  apply eval_shr; auto.
  caseEq (Int.ltu i0 (Int.repr 32)); intro; rewrite H2 in H1; inv H1.
  apply eval_shru; auto.
  EvalOp.
  EvalOp.
  EvalOp.
  EvalOp.
  apply eval_comp_int; auto.
  eapply eval_comp_int_ptr; eauto.
  eapply eval_comp_ptr_int; eauto.
  generalize H1; clear H1.
  case_eq (valid_pointer m b (Int.signed i) && valid_pointer m b0 (Int.signed i0)); intros.
  destruct (eq_block b b0); inv H2.
  eapply eval_comp_ptr_ptr; eauto.
  eapply eval_comp_ptr_ptr_2; eauto.
  discriminate.
  eapply eval_compu; eauto.
  eapply eval_compf; eauto.
Qed.

End CMCONSTR.

(** * Semantic preservation for instruction selection. *)

Section PRESERVATION.

Variable prog: Cminor.program.
Let tprog := sel_program prog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

(** Relationship between the global environments for the original
  CminorSel program and the generated RTL program. *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros; unfold ge, tge, tprog, sel_program. 
  apply Genv.find_symbol_transf.
Qed.

Lemma functions_translated:
  forall (v: val) (f: Cminor.fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (sel_fundef f).
Proof.  
  intros.
  exact (Genv.find_funct_transf sel_fundef H).
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: Cminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (sel_fundef f).
Proof.  
  intros. 
  exact (Genv.find_funct_ptr_transf sel_fundef H).
Qed.

Lemma sig_function_translated:
  forall f,
  funsig (sel_fundef f) = Cminor.funsig f.
Proof.
  intros. destruct f; reflexivity.
Qed.

(** Semantic preservation for expressions. *)

Lemma sel_expr_correct:
  forall sp e m a v,
  Cminor.eval_expr ge sp e m a v ->
  forall le,
  eval_expr tge sp e m le (sel_expr a) v.
Proof.
  induction 1; intros; simpl.
  (* Evar *)
  constructor; auto.
  (* Econst *)
  destruct cst; simpl; simpl in H; (econstructor; [constructor|simpl;auto]).
  rewrite symbols_preserved. auto.
  (* Eunop *)
  eapply eval_sel_unop; eauto.
  (* Ebinop *)
  eapply eval_sel_binop; eauto.
  (* Eload *)
  eapply eval_load; eauto.
  (* Econdition *)
  econstructor; eauto. eapply eval_condition_of_expr; eauto. 
  destruct b1; auto.
Qed.

Hint Resolve sel_expr_correct: evalexpr.

Lemma sel_exprlist_correct:
  forall sp e m a v,
  Cminor.eval_exprlist ge sp e m a v ->
  forall le,
  eval_exprlist tge sp e m le (sel_exprlist a) v.
Proof.
  induction 1; intros; simpl; constructor; auto with evalexpr.
Qed.

Hint Resolve sel_exprlist_correct: evalexpr.

(** Semantic preservation for terminating function calls and statements. *)

Fixpoint sel_cont (k: Cminor.cont) : CminorSel.cont :=
  match k with
  | Cminor.Kstop => Kstop
  | Cminor.Kseq s1 k1 => Kseq (sel_stmt s1) (sel_cont k1)
  | Cminor.Kblock k1 => Kblock (sel_cont k1)
  | Cminor.Kcall id f sp e k1 =>
      Kcall id (sel_function f) sp e (sel_cont k1)
  end.

Inductive match_states: Cminor.state -> CminorSel.state -> Prop :=
  | match_state: forall f s k s' k' sp e m,
      s' = sel_stmt s ->
      k' = sel_cont k ->
      match_states
        (Cminor.State f s k sp e m)
        (State (sel_function f) s' k' sp e m)
  | match_callstate: forall f args k k' m,
      k' = sel_cont k ->
      match_states
        (Cminor.Callstate f args k m)
        (Callstate (sel_fundef f) args k' m)
  | match_returnstate: forall v k k' m,
      k' = sel_cont k ->
      match_states
        (Cminor.Returnstate v k m)
        (Returnstate v k' m).

Remark call_cont_commut:
  forall k, call_cont (sel_cont k) = sel_cont (Cminor.call_cont k).
Proof.
  induction k; simpl; auto.
Qed.

Remark find_label_commut:
  forall lbl s k,
  find_label lbl (sel_stmt s) (sel_cont k) =
  option_map (fun sk => (sel_stmt (fst sk), sel_cont (snd sk)))
             (Cminor.find_label lbl s k).
Proof.
  induction s; intros; simpl; auto.
  unfold store. destruct (addressing m (sel_expr e)); auto.
  change (Kseq (sel_stmt s2) (sel_cont k))
    with (sel_cont (Cminor.Kseq s2 k)).
  rewrite IHs1. rewrite IHs2. 
  destruct (Cminor.find_label lbl s1 (Cminor.Kseq s2 k)); auto.
  rewrite IHs1. rewrite IHs2. 
  destruct (Cminor.find_label lbl s1 k); auto.
  change (Kseq (Sloop (sel_stmt s)) (sel_cont k))
    with (sel_cont (Cminor.Kseq (Cminor.Sloop s) k)).
  auto.
  change (Kblock (sel_cont k))
    with (sel_cont (Cminor.Kblock k)).
  auto.
  destruct o; auto.
  destruct (ident_eq lbl l); auto.
Qed.

Lemma sel_step_correct:
  forall S1 t S2, Cminor.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
  exists T2, step tge T1 t T2 /\ match_states S2 T2.
Proof.
  induction 1; intros T1 ME; inv ME; simpl;
  try (econstructor; split; [econstructor; eauto with evalexpr | econstructor; eauto]; fail).

  (* skip call *)
  econstructor; split. 
  econstructor. destruct k; simpl in H; simpl; auto. 
  rewrite <- H0; reflexivity.
  constructor; auto.
  (* assign *)
  exists (State (sel_function f) Sskip (sel_cont k) sp (PTree.set id v e) m); split.
  constructor. auto with evalexpr.
  constructor; auto.
  (* store *)
  econstructor; split.
  eapply eval_store; eauto with evalexpr.
  constructor; auto.
  (* Scall *)
  econstructor; split.
  econstructor; eauto with evalexpr.
  apply functions_translated; eauto. 
  apply sig_function_translated.
  constructor; auto.
  (* Stailcall *)
  econstructor; split.
  econstructor; eauto with evalexpr.
  apply functions_translated; eauto. 
  apply sig_function_translated.
  constructor; auto. apply call_cont_commut.
  (* Salloc *)
  exists (State (sel_function f) Sskip (sel_cont k) sp (PTree.set id (Vptr b Int.zero) e) m'); split.
  econstructor; eauto with evalexpr.
  constructor; auto.
  (* Sifthenelse *)
  exists (State (sel_function f) (if b then sel_stmt s1 else sel_stmt s2) (sel_cont k) sp e m); split.
  constructor. eapply eval_condition_of_expr; eauto with evalexpr.
  constructor; auto. destruct b; auto.
  (* Sreturn None *)
  econstructor; split. 
  econstructor. 
  constructor; auto. apply call_cont_commut.
  (* Sreturn Some *)
  econstructor; split. 
  econstructor. simpl. eauto with evalexpr. 
  constructor; auto. apply call_cont_commut.
  (* Sgoto *)
  econstructor; split.
  econstructor. simpl. rewrite call_cont_commut. rewrite find_label_commut.
  rewrite H. simpl. reflexivity. 
  constructor; auto.
Qed.

Lemma sel_initial_states:
  forall S, Cminor.initial_state prog S ->
  exists R, initial_state tprog R /\ match_states S R.
Proof.
  induction 1.
  econstructor; split.
  econstructor.
  simpl. fold tge. rewrite symbols_preserved. eexact H.
  apply function_ptr_translated. eauto. 
  rewrite <- H1. apply sig_function_translated; auto.
  unfold tprog, sel_program. rewrite Genv.init_mem_transf.
  constructor; auto.
Qed.

Lemma sel_final_states:
  forall S R r,
  match_states S R -> Cminor.final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H. simpl. constructor.
Qed.

Theorem transf_program_correct:
  forall (beh: program_behavior),
  Cminor.exec_program prog beh -> CminorSel.exec_program tprog beh.
Proof.
  unfold CminorSel.exec_program, Cminor.exec_program; intros.
  eapply simulation_step_preservation; eauto.
  eexact sel_initial_states.
  eexact sel_final_states.
  exact sel_step_correct. 
Qed.

End PRESERVATION.

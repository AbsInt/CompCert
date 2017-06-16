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

(** Correctness of instruction selection for operators *)

Require Import Coqlib.
Require Import Maps.
Require Import Compopts.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.

Open Local Scope cminorsel_scope.

(** * Useful lemmas and tactics *)

(** The following are trivial lemmas and custom tactics that help
  perform backward (inversion) and forward reasoning over the evaluation
  of operator applications. *)

Ltac EvalOp := eapply eval_Eop; eauto with evalexpr.

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

Ltac TrivialExists :=
  match goal with
  | [ |- exists v, _ /\ Val.lessdef ?a v ] => exists a; split; [EvalOp | auto]
  end.

(** * Correctness of the smart constructors *)

Section CMCONSTR.

Variable ge: genv.
Variable sp: val.
Variable e: env.
Variable m: mem.

(** We now show that the code generated by "smart constructor" functions
  such as [SelectOp.notint] behaves as expected.  Continuing the
  [notint] example, we show that if the expression [e]
  evaluates to some value [v], then [SelectOp.notint e]
  evaluates to a value [v'] which is either [Val.notint v] or more defined
  than [Val.notint v].

  All proofs follow a common pattern:
- Reasoning by case over the result of the classification functions
  (such as [add_match] for integer addition), gathering additional
  information on the shape of the argument expressions in the non-default
  cases.
- Inversion of the evaluations of the arguments, exploiting the additional
  information thus gathered.
- Equational reasoning over the arithmetic operations performed,
  using the lemmas from the [Int], [Float] and [Value] modules.
- Construction of an evaluation derivation for the expression returned
  by the smart constructor.
*)

Definition unary_constructor_sound (cstr: expr -> expr) (sem: val -> val) : Prop :=
  forall le a x,
  eval_expr ge sp e m le a x ->
  exists v, eval_expr ge sp e m le (cstr a) v /\ Val.lessdef (sem x) v.

Definition binary_constructor_sound (cstr: expr -> expr -> expr) (sem: val -> val -> val) : Prop :=
  forall le a x b y,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  exists v, eval_expr ge sp e m le (cstr a b) v /\ Val.lessdef (sem x y) v.

Theorem eval_addrsymbol:
  forall le id ofs,
  exists v, eval_expr ge sp e m le (addrsymbol id ofs) v /\ Val.lessdef (Genv.symbol_address ge id ofs) v.
Proof.
  intros. unfold addrsymbol. econstructor; split.
  EvalOp. simpl; eauto.
  auto.
Qed.

Theorem eval_addrstack:
  forall le ofs,
  exists v, eval_expr ge sp e m le (addrstack ofs) v /\ Val.lessdef (Val.add sp (Vint ofs)) v.
Proof.
  intros. unfold addrstack. econstructor; split.
  EvalOp. simpl; eauto.
  auto.
Qed.

Theorem eval_notint: unary_constructor_sound notint Val.notint.
Proof.
  assert (forall v, Val.lessdef (Val.notint (Val.notint v)) v).
    destruct v; simpl; auto. rewrite Int.not_involutive; auto.
  unfold notint; red; intros until x; case (notint_match a); intros; InvEval.
  TrivialExists.
  subst. exists v1; split; auto.
  subst. TrivialExists.
  subst. TrivialExists.
  subst. TrivialExists.
  subst. exists (Val.and v1 v0); split; auto. EvalOp.
  subst. exists (Val.or v1 v0); split; auto. EvalOp.
  subst. exists (Val.xor v1 v0); split; auto. EvalOp.
  subst. exists (Val.or v0 (Val.notint v1)); split. EvalOp.
    destruct v0; destruct v1; simpl; auto. rewrite Int.not_and_or_not. rewrite Int.not_involutive.
    rewrite Int.or_commut. auto.
  subst. exists (Val.and v0 (Val.notint v1)); split. EvalOp.
    destruct v0; destruct v1; simpl; auto. rewrite Int.not_or_and_not. rewrite Int.not_involutive.
    rewrite Int.and_commut. auto.
  subst x. TrivialExists. simpl. rewrite Val.not_xor. rewrite Val.xor_assoc. auto.
  TrivialExists.
Qed.

Theorem eval_addimm:
  forall n, unary_constructor_sound (addimm n) (fun x => Val.add x (Vint n)).
Proof.
  red; unfold addimm; intros until x.
  predSpec Int.eq Int.eq_spec n Int.zero.
  subst n. intros. exists x; split; auto.
  destruct x; simpl; auto. rewrite Int.add_zero. auto. rewrite Int.add_zero. auto.
  case (addimm_match a); intros; InvEval; simpl; TrivialExists; simpl.
  rewrite Int.add_commut. auto.
  unfold Genv.symbol_address. destruct (Genv.find_symbol ge s); simpl; auto. rewrite Int.add_commut; auto.
  rewrite Val.add_assoc. rewrite Int.add_commut. auto.
  subst. rewrite Val.add_assoc. rewrite Int.add_commut. auto.
  subst. rewrite Int.add_commut. rewrite Genv.shift_symbol_address. rewrite ! Val.add_assoc. f_equal. f_equal. apply Val.add_commut.
Qed.

Theorem eval_addsymbol:
  forall s ofs, unary_constructor_sound (addsymbol s ofs) (Val.add (Genv.symbol_address ge s ofs)).
Proof.
  red; unfold addsymbol; intros until x.
  case (addsymbol_match a); intros; InvEval; simpl; TrivialExists; simpl.
  rewrite Genv.shift_symbol_address. auto.
  rewrite Genv.shift_symbol_address. subst x. rewrite Val.add_assoc. f_equal. f_equal.
  apply Val.add_commut.
Qed.

Theorem eval_add: binary_constructor_sound add Val.add.
Proof.
  red; intros until y.
  unfold add; case (add_match a b); intros; InvEval.
- rewrite Val.add_commut. apply eval_addimm; auto.
- apply eval_addimm; auto.
- apply eval_addsymbol; auto.
- rewrite Val.add_commut. apply eval_addsymbol; auto.
- subst.
  replace (Val.add (Val.add v1 (Vint n1)) (Val.add v0 (Vint n2)))
     with (Val.add (Val.add v1 v0) (Val.add (Vint n1) (Vint n2))).
  apply eval_addimm. EvalOp.
  repeat rewrite Val.add_assoc. decEq. apply Val.add_permut.
- subst.
  replace (Val.add (Val.add v1 (Vint n1)) y)
     with (Val.add (Val.add v1 y) (Vint n1)).
  apply eval_addimm. EvalOp.
  repeat rewrite Val.add_assoc. decEq. apply Val.add_commut.
- subst. TrivialExists.
    econstructor. EvalOp. simpl. reflexivity. econstructor. eauto. constructor.
    simpl. repeat rewrite Val.add_assoc. decEq; decEq.
    rewrite Val.add_commut. rewrite Val.add_permut. auto.
- replace (Val.add x y) with
    (Val.add (Genv.symbol_address ge s (Int.add ofs n)) (Val.add v1 v0)).
  apply eval_addsymbol; auto. EvalOp.
  subst. rewrite Genv.shift_symbol_address. rewrite ! Val.add_assoc. f_equal.
  rewrite Val.add_permut. f_equal. apply Val.add_commut.
- subst. rewrite Val.add_assoc. apply eval_addsymbol. EvalOp.
- subst. rewrite <- Val.add_assoc. apply eval_addimm. EvalOp.
- subst. rewrite Val.add_permut. apply eval_addsymbol. EvalOp.
- TrivialExists.
Qed.

Theorem eval_subimm:
  forall n, unary_constructor_sound (subimm n) (fun v => Val.sub (Vint n) v).
Proof.
  intros; red; intros until x. unfold subimm. destruct (subimm_match a); intros.
  InvEval. TrivialExists.
  InvEval. subst x. TrivialExists. unfold eval_operation. destruct v1; simpl; auto.
  rewrite ! Int.sub_add_opp. rewrite Int.add_assoc. f_equal. f_equal. f_equal.
  rewrite Int.neg_add_distr.  apply Int.add_commut.
  TrivialExists.
Qed.

Theorem eval_sub: binary_constructor_sound sub Val.sub.
Proof.
  red; intros until y.
  unfold sub; case (sub_match a b); intros; InvEval.
  rewrite Val.sub_add_opp. apply eval_addimm; auto.
  apply eval_subimm; auto.
  subst. rewrite Val.sub_add_l. rewrite Val.sub_add_r.
    rewrite Val.add_assoc. simpl. rewrite Int.add_commut. rewrite <- Int.sub_add_opp.
    apply eval_addimm; EvalOp.
  subst. rewrite Val.sub_add_l. apply eval_addimm; EvalOp.
  subst. rewrite Val.sub_add_r. apply eval_addimm; EvalOp.
  TrivialExists.
Qed.

Theorem eval_negint: unary_constructor_sound negint (fun v => Val.sub Vzero v).
Proof.
  red; intros. unfold negint. apply eval_subimm; auto.
Qed.

Lemma eval_rolm:
  forall amount mask,
  unary_constructor_sound (fun a => rolm a amount mask)
                          (fun x => Val.rolm x amount mask).
Proof.
  red; intros until x. unfold rolm; case (rolm_match a); intros; InvEval.
  TrivialExists.
  subst. rewrite Val.rolm_rolm. TrivialExists.
  subst. rewrite <- Val.rolm_zero. rewrite Val.rolm_rolm.
  rewrite (Int.add_commut Int.zero). rewrite Int.add_zero. TrivialExists.
  TrivialExists.
Qed.

Theorem eval_shlimm:
  forall n, unary_constructor_sound (fun a => shlimm a n)
                                    (fun x => Val.shl x (Vint n)).
Proof.
  red; intros.  unfold shlimm.
  predSpec Int.eq Int.eq_spec n Int.zero.
  subst. exists x; split; auto. destruct x; simpl; auto. rewrite Int.shl_zero; auto.
  destruct (Int.ltu n Int.iwordsize) eqn:?.
  rewrite Val.shl_rolm; auto. apply eval_rolm; auto.
  TrivialExists. econstructor. eauto. econstructor. EvalOp. simpl; eauto. constructor. auto.
Qed.

Theorem eval_shruimm:
  forall n, unary_constructor_sound (fun a => shruimm a n)
                                    (fun x => Val.shru x (Vint n)).
Proof.
  red; intros.  unfold shruimm.
  predSpec Int.eq Int.eq_spec n Int.zero.
  subst. exists x; split; auto. destruct x; simpl; auto. rewrite Int.shru_zero; auto.
  destruct (Int.ltu n Int.iwordsize) eqn:?.
  rewrite Val.shru_rolm; auto. apply eval_rolm; auto.
  TrivialExists. econstructor. eauto. econstructor. EvalOp. simpl; eauto. constructor. auto.
Qed.

Theorem eval_shrimm:
  forall n, unary_constructor_sound (fun a => shrimm a n)
                                    (fun x => Val.shr x (Vint n)).
Proof.
  red; intros until x. unfold shrimm.
  predSpec Int.eq Int.eq_spec n Int.zero.
  intros. subst. exists x; split; auto. destruct x; simpl; auto. rewrite Int.shr_zero; auto.
  destruct (Int.ltu n Int.iwordsize) eqn:WS.
  case (shrimm_match a); intros.
  InvEval. exists (Vint (Int.shr n1 n)); split. EvalOp. simpl; rewrite WS; auto.
  simpl; destruct (Int.lt mask1 Int.zero) eqn:?.
  TrivialExists.
  replace (Val.shr x (Vint n)) with (Val.shru x (Vint n)).
  apply eval_shruimm; auto.
  destruct x; simpl; auto. rewrite WS.
  decEq. symmetry. InvEval. destruct v1; simpl in H0; inv H0.
  apply Int.shr_and_is_shru_and; auto.
  simpl. TrivialExists.
  intros. simpl. TrivialExists.
  constructor. eauto. constructor. EvalOp. simpl; eauto. constructor. auto.
Qed.

Lemma eval_mulimm_base:
  forall n, unary_constructor_sound (mulimm_base n) (fun x => Val.mul x (Vint n)).
Proof.
  intros; red; intros; unfold mulimm_base.
  generalize (Int.one_bits_decomp n).
  generalize (Int.one_bits_range n).
  destruct (Int.one_bits n).
  intros. TrivialExists.
  destruct l.
  intros. rewrite H1. simpl.
  rewrite Int.add_zero.
  replace (Vint (Int.shl Int.one i)) with (Val.shl Vone (Vint i)). rewrite Val.shl_mul.
  apply eval_shlimm. auto. simpl. rewrite H0; auto with coqlib.
  destruct l.
  intros. destruct (optim_for_size tt). TrivialExists.
  rewrite H1. simpl.
  exploit (eval_shlimm i (x :: le) (Eletvar 0) x). constructor; auto. intros [v1 [A1 B1]].
  exploit (eval_shlimm i0 (x :: le) (Eletvar 0) x). constructor; auto. intros [v2 [A2 B2]].
  exists (Val.add v1 v2); split.
  econstructor. eauto. EvalOp.
  rewrite Int.add_zero.
  replace (Vint (Int.add (Int.shl Int.one i) (Int.shl Int.one i0)))
     with (Val.add (Val.shl Vone (Vint i)) (Val.shl Vone (Vint i0))).
  rewrite Val.mul_add_distr_r.
  repeat rewrite Val.shl_mul. apply Val.add_lessdef; auto.
  simpl. repeat rewrite H0; auto with coqlib.
  intros. TrivialExists.
Qed.

Theorem eval_mulimm:
  forall n, unary_constructor_sound (mulimm n) (fun x => Val.mul x (Vint n)).
Proof.
  intros; red; intros until x; unfold mulimm.
  predSpec Int.eq Int.eq_spec n Int.zero.
  intros. exists (Vint Int.zero); split. EvalOp.
  destruct x; simpl; auto. subst n. rewrite Int.mul_zero. auto.
  predSpec Int.eq Int.eq_spec n Int.one.
  intros. exists x; split; auto.
  destruct x; simpl; auto. subst n. rewrite Int.mul_one. auto.
  case (mulimm_match a); intros; InvEval.
  TrivialExists. simpl. rewrite Int.mul_commut; auto.
  subst. rewrite Val.mul_add_distr_l.
  exploit eval_mulimm_base; eauto. instantiate (1 := n). intros [v' [A1 B1]].
  exploit (eval_addimm (Int.mul n n2) le (mulimm_base n t2) v'). auto. intros [v'' [A2 B2]].
  exists v''; split; auto. eapply Val.lessdef_trans. eapply Val.add_lessdef; eauto.
  rewrite Val.mul_commut; auto.
  apply eval_mulimm_base; auto.
Qed.

Theorem eval_mul: binary_constructor_sound mul Val.mul.
Proof.
  red; intros until y.
  unfold mul; case (mul_match a b); intros; InvEval.
  rewrite Val.mul_commut. apply eval_mulimm. auto.
  apply eval_mulimm. auto.
  TrivialExists.
Qed.

Theorem eval_andimm:
  forall n, unary_constructor_sound (andimm n) (fun x => Val.and x (Vint n)).
Proof.
  intros; red; intros until x. unfold andimm.
  predSpec Int.eq Int.eq_spec n Int.zero.
  intros. subst. exists (Vint Int.zero); split. EvalOp.
  destruct x; simpl; auto. rewrite Int.and_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.mone.
  intros. subst. exists x; split. auto.
  destruct x; simpl; auto. rewrite Int.and_mone; auto.
  clear H H0.
  case (andimm_match a); intros.
  InvEval. TrivialExists. simpl. rewrite Int.and_commut; auto.
  set (n' := Int.and n n2).
  destruct (Int.eq (Int.shru (Int.shl n' amount) amount) n' &&
            Int.ltu amount Int.iwordsize) eqn:?.
  InvEval. destruct (andb_prop _ _ Heqb).
  generalize (Int.eq_spec (Int.shru (Int.shl n' amount) amount) n'). rewrite H1; intros.
  replace (Val.and x (Vint n))
     with (Val.rolm v0 (Int.sub Int.iwordsize amount) (Int.and (Int.shru Int.mone amount) n')).
  apply eval_rolm; auto.
  subst. destruct v0; simpl; auto. rewrite H3. simpl. decEq. rewrite Int.and_assoc.
  rewrite (Int.and_commut n2 n).
  transitivity (Int.and (Int.shru i amount) (Int.and n n2)).
  rewrite (Int.shru_rolm i); auto. unfold Int.rolm. rewrite Int.and_assoc; auto.
  symmetry. apply Int.shr_and_shru_and. auto.
  set (e2 := Eop (Oshrimm amount) (t2 ::: Enil)) in *.
  InvEval. subst. rewrite Val.and_assoc. simpl. rewrite Int.and_commut. TrivialExists.
  InvEval. subst. rewrite Val.and_assoc. simpl. rewrite Int.and_commut. TrivialExists.
  InvEval. subst. TrivialExists. simpl.
  destruct v1; auto. simpl. unfold Int.rolm. rewrite Int.and_assoc.
  decEq. decEq. decEq. apply Int.and_commut.
  destruct (Int.eq (Int.shru (Int.shl n amount) amount) n &&
            Int.ltu amount Int.iwordsize) eqn:?.
  InvEval. destruct (andb_prop _ _ Heqb).
  generalize (Int.eq_spec (Int.shru (Int.shl n amount) amount) n). rewrite H0; intros.
  replace (Val.and x (Vint n))
     with (Val.rolm v1 (Int.sub Int.iwordsize amount) (Int.and (Int.shru Int.mone amount) n)).
  apply eval_rolm; auto.
  subst x. destruct v1; simpl; auto. rewrite H1; simpl. decEq.
  transitivity (Int.and (Int.shru i amount) n).
  rewrite (Int.shru_rolm i); auto. unfold Int.rolm. rewrite Int.and_assoc; auto.
  symmetry. apply Int.shr_and_shru_and. auto.
  TrivialExists.
  TrivialExists.
Qed.

Theorem eval_and: binary_constructor_sound and Val.and.
Proof.
  red; intros until y; unfold and; case (and_match a b); intros; InvEval.
  rewrite Val.and_commut. apply eval_andimm; auto.
  apply eval_andimm; auto.
  subst. rewrite Val.and_commut. TrivialExists.
  subst. TrivialExists.
  TrivialExists.
Qed.

Theorem eval_orimm:
  forall n, unary_constructor_sound (orimm n) (fun x => Val.or x (Vint n)).
Proof.
  intros; red; intros until x. unfold orimm.
  predSpec Int.eq Int.eq_spec n Int.zero.
  intros. subst. exists x; split; auto. destruct x; simpl; auto. rewrite Int.or_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.mone.
  intros. subst. exists (Vint Int.mone); split. EvalOp. destruct x; simpl; auto. rewrite Int.or_mone; auto.
  clear H H0. destruct (orimm_match a); intros; InvEval.
  TrivialExists. simpl. rewrite Int.or_commut; auto.
  subst. rewrite Val.or_assoc. simpl. rewrite Int.or_commut. TrivialExists.
  TrivialExists.
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

Theorem eval_or: binary_constructor_sound or Val.or.
Proof.
  red; intros until y; unfold or; case (or_match a b); intros.
(* rolm - rolm *)
  destruct (Int.eq amount1 amount2 && same_expr_pure t1 t2) eqn:?.
  destruct (andb_prop _ _ Heqb0).
  generalize (Int.eq_spec amount1 amount2). rewrite H1. intro. subst amount2.
  InvEval. exploit eval_same_expr; eauto. intros [EQ1 EQ2]. subst.
  rewrite Val.or_rolm. TrivialExists.
  TrivialExists.
(* andimm - rolm *)
  destruct (Int.eq mask1 (Int.not mask2) && is_rlw_mask mask2) eqn:?.
  destruct (andb_prop _ _ Heqb0).
  generalize (Int.eq_spec mask1 (Int.not mask2)); rewrite H1; intros.
  InvEval. subst. TrivialExists.
  TrivialExists.
(* rolm - andimm *)
  destruct (Int.eq mask2 (Int.not mask1) && is_rlw_mask mask1) eqn:?.
  destruct (andb_prop _ _ Heqb0).
  generalize (Int.eq_spec mask2 (Int.not mask1)); rewrite H1; intros.
  InvEval. subst. rewrite Val.or_commut. TrivialExists.
  TrivialExists.
(* intconst *)
  InvEval. rewrite Val.or_commut. apply eval_orimm; auto.
  InvEval. apply eval_orimm; auto.
(* orc *)
  InvEval. subst. rewrite Val.or_commut. TrivialExists.
  InvEval. subst. TrivialExists.
(* default *)
  TrivialExists.
Qed.

Theorem eval_xorimm:
  forall n, unary_constructor_sound (xorimm n) (fun x => Val.xor x (Vint n)).
Proof.
  intros; red; intros until x. unfold xorimm.
  predSpec Int.eq Int.eq_spec n Int.zero.
  intros. subst. exists x; split; auto. destruct x; simpl; auto. rewrite Int.xor_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.mone.
  intros. subst. rewrite <- Val.not_xor. apply eval_notint; auto.
  clear H H0. destruct (xorimm_match a); intros; InvEval.
  TrivialExists. simpl. rewrite Int.xor_commut; auto.
  subst. rewrite Val.xor_assoc. simpl. rewrite Int.xor_commut. TrivialExists.
  subst x. TrivialExists. simpl. rewrite Val.not_xor. rewrite Val.xor_assoc.
  simpl. rewrite Int.xor_commut; auto.
  TrivialExists.
Qed.

Theorem eval_xor: binary_constructor_sound xor Val.xor.
Proof.
  red; intros until y; unfold xor; case (xor_match a b); intros; InvEval.
  rewrite Val.xor_commut. apply eval_xorimm; auto.
  apply eval_xorimm; auto.
  subst. rewrite Val.xor_commut. rewrite Val.not_xor. rewrite <- Val.xor_assoc.
  rewrite <- Val.not_xor. rewrite Val.xor_commut. TrivialExists.
  subst. rewrite Val.not_xor. rewrite <- Val.xor_assoc. rewrite <- Val.not_xor. TrivialExists.
  TrivialExists.
Qed.

Theorem eval_divs_base:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.divs x y = Some z ->
  exists v, eval_expr ge sp e m le (divs_base a b) v /\ Val.lessdef z v.
Proof.
  intros. unfold divs_base. exists z; split. EvalOp. auto.
Qed.

Lemma eval_mod_aux:
  forall divop semdivop,
  (forall sp x y m, eval_operation ge sp divop (x :: y :: nil) m = semdivop x y) ->
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  semdivop x y = Some z ->
  eval_expr ge sp e m le (mod_aux divop a b) (Val.sub x (Val.mul z y)).
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
  rewrite H. eauto.
  eapply eval_Econs. apply eval_Eletvar. simpl; reflexivity.
  apply eval_Enil.
  simpl; reflexivity. apply eval_Enil.
  reflexivity.
Qed.

Theorem eval_mods_base:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.mods x y = Some z ->
  exists v, eval_expr ge sp e m le (mods_base a b) v /\ Val.lessdef z v.
Proof.
  intros; unfold mods_base.
  exploit Val.mods_divs; eauto. intros [v [A B]].
  subst. econstructor; split; eauto.
  apply eval_mod_aux with (semdivop := Val.divs); auto.
Qed.

Theorem eval_divu_base:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.divu x y = Some z ->
  exists v, eval_expr ge sp e m le (divu_base a b) v /\ Val.lessdef z v.
Proof.
  intros. unfold divu_base. exists z; split. EvalOp. auto.
Qed.

Theorem eval_modu_base:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.modu x y = Some z ->
  exists v, eval_expr ge sp e m le (modu_base a b) v /\ Val.lessdef z v.
Proof.
  intros; unfold modu_base.
  exploit Val.modu_divu; eauto. intros [v [A B]].
  subst. econstructor; split; eauto.
  apply eval_mod_aux with (semdivop := Val.divu); auto.
Qed.

Theorem eval_shrximm:
  forall le a n x z,
  eval_expr ge sp e m le a x ->
  Val.shrx x (Vint n) = Some z ->
  exists v, eval_expr ge sp e m le (shrximm a n) v /\ Val.lessdef z v.
Proof.
  intros. unfold shrximm.
  predSpec Int.eq Int.eq_spec n Int.zero.
  subst n. exists x; split; auto.
  destruct x; simpl in H0; try discriminate.
  destruct (Int.ltu Int.zero (Int.repr 31)); inv H0.
  replace (Int.shrx i Int.zero) with i. auto.
  unfold Int.shrx, Int.divs. rewrite Int.shl_zero.
  change (Int.signed Int.one) with 1. rewrite Z.quot_1_r. rewrite Int.repr_signed; auto.
  econstructor; split. EvalOp. auto.
Qed.

Theorem eval_shl: binary_constructor_sound shl Val.shl.
Proof.
  red; intros until y; unfold shl; case (shl_match b); intros.
  InvEval. apply eval_shlimm; auto.
  TrivialExists.
Qed.

Theorem eval_shr: binary_constructor_sound shr Val.shr.
Proof.
  red; intros until y; unfold shr; case (shr_match b); intros.
  InvEval. apply eval_shrimm; auto.
  TrivialExists.
Qed.

Theorem eval_shru: binary_constructor_sound shru Val.shru.
Proof.
  red; intros until y; unfold shru; case (shru_match b); intros.
  InvEval. apply eval_shruimm; auto.
  TrivialExists.
Qed.

Theorem eval_negf: unary_constructor_sound negf Val.negf.
Proof.
  red; intros. TrivialExists.
Qed.

Theorem eval_absf: unary_constructor_sound absf Val.absf.
Proof.
  red; intros. TrivialExists.
Qed.

Theorem eval_addf: binary_constructor_sound addf Val.addf.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_subf: binary_constructor_sound subf Val.subf.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_mulf: binary_constructor_sound mulf Val.mulf.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_negfs: unary_constructor_sound negfs Val.negfs.
Proof.
  red; intros. TrivialExists.
Qed.

Theorem eval_absfs: unary_constructor_sound absfs Val.absfs.
Proof.
  red; intros. TrivialExists.
Qed.

Theorem eval_addfs: binary_constructor_sound addfs Val.addfs.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_subfs: binary_constructor_sound subfs Val.subfs.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_mulfs: binary_constructor_sound mulfs Val.mulfs.
Proof.
  red; intros; TrivialExists.
Qed.

Section COMP_IMM.

Variable default: comparison -> int -> condition.
Variable intsem: comparison -> int -> int -> bool.
Variable sem: comparison -> val -> val -> val.

Hypothesis sem_int: forall c x y, sem c (Vint x) (Vint y) = Val.of_bool (intsem c x y).
Hypothesis sem_undef: forall c v, sem c Vundef v = Vundef.
Hypothesis sem_eq: forall x y, sem Ceq (Vint x) (Vint y) = Val.of_bool (Int.eq x y).
Hypothesis sem_ne: forall x y, sem Cne (Vint x) (Vint y) = Val.of_bool (negb (Int.eq x y)).
Hypothesis sem_default: forall c v n, sem c v (Vint n) = Val.of_optbool (eval_condition (default c n) (v :: nil) m).

Lemma eval_compimm:
  forall le c a n2 x,
  eval_expr ge sp e m le a x ->
  exists v, eval_expr ge sp e m le (compimm default intsem c a n2) v
         /\ Val.lessdef (sem c x (Vint n2)) v.
Proof.
  intros until x.
  unfold compimm; case (compimm_match c a); intros.
(* constant *)
  InvEval. rewrite sem_int. TrivialExists. simpl. destruct (intsem c0 n1 n2); auto.
(* eq cmp *)
  InvEval. inv H. simpl in H5. inv H5.
  destruct (Int.eq_dec n2 Int.zero). subst n2. TrivialExists.
  simpl. rewrite eval_negate_condition.
  destruct (eval_condition c0 vl m); simpl.
  unfold Vtrue, Vfalse. destruct b; simpl; rewrite sem_eq; auto.
  rewrite sem_undef; auto.
  destruct (Int.eq_dec n2 Int.one). subst n2. TrivialExists.
  simpl. destruct (eval_condition c0 vl m); simpl.
  unfold Vtrue, Vfalse. destruct b; simpl; rewrite sem_eq; auto.
  rewrite sem_undef; auto.
  exists (Vint Int.zero); split. EvalOp.
  destruct (eval_condition c0 vl m); simpl.
  unfold Vtrue, Vfalse. destruct b; rewrite sem_eq; rewrite Int.eq_false; auto.
  rewrite sem_undef; auto.
(* ne cmp *)
  InvEval. inv H. simpl in H5. inv H5.
  destruct (Int.eq_dec n2 Int.zero). subst n2. TrivialExists.
  simpl. destruct (eval_condition c0 vl m); simpl.
  unfold Vtrue, Vfalse. destruct b; simpl; rewrite sem_ne; auto.
  rewrite sem_undef; auto.
  destruct (Int.eq_dec n2 Int.one). subst n2. TrivialExists.
  simpl. rewrite eval_negate_condition. destruct (eval_condition c0 vl m); simpl.
  unfold Vtrue, Vfalse. destruct b; simpl; rewrite sem_ne; auto.
  rewrite sem_undef; auto.
  exists (Vint Int.one); split. EvalOp.
  destruct (eval_condition c0 vl m); simpl.
  unfold Vtrue, Vfalse. destruct b; rewrite sem_ne; rewrite Int.eq_false; auto.
  rewrite sem_undef; auto.
(* eq andimm *)
  destruct (Int.eq_dec n2 Int.zero). InvEval; subst.
  econstructor; split. EvalOp. simpl; eauto.
  destruct v1; simpl; try (rewrite sem_undef; auto). rewrite sem_eq.
  destruct (Int.eq (Int.and i n1) Int.zero); auto.
  TrivialExists. simpl. rewrite sem_default. auto.
(* ne andimm *)
  destruct (Int.eq_dec n2 Int.zero). InvEval; subst.
  econstructor; split. EvalOp. simpl; eauto.
  destruct v1; simpl; try (rewrite sem_undef; auto). rewrite sem_ne.
  destruct (Int.eq (Int.and i n1) Int.zero); auto.
  TrivialExists. simpl. rewrite sem_default. auto.
(* default *)
  TrivialExists. simpl. rewrite sem_default. auto.
Qed.

Hypothesis sem_swap:
  forall c x y, sem (swap_comparison c) x y = sem c y x.

Lemma eval_compimm_swap:
  forall le c a n2 x,
  eval_expr ge sp e m le a x ->
  exists v, eval_expr ge sp e m le (compimm default intsem (swap_comparison c) a n2) v
         /\ Val.lessdef (sem c (Vint n2) x) v.
Proof.
  intros. rewrite <- sem_swap. eapply eval_compimm; eauto.
Qed.

End COMP_IMM.

Theorem eval_comp:
  forall c, binary_constructor_sound (comp c) (Val.cmp c).
Proof.
  intros; red; intros until y. unfold comp; case (comp_match a b); intros; InvEval.
  eapply eval_compimm_swap; eauto.
  intros. unfold Val.cmp. rewrite Val.swap_cmp_bool; auto.
  eapply eval_compimm; eauto.
  TrivialExists.
Qed.

Theorem eval_compu:
  forall c, binary_constructor_sound (compu c) (Val.cmpu (Mem.valid_pointer m) c).
Proof.
  intros; red; intros until y. unfold compu; case (compu_match a b); intros; InvEval.
  eapply eval_compimm_swap; eauto.
  intros. unfold Val.cmpu. rewrite Val.swap_cmpu_bool; auto.
  eapply eval_compimm; eauto.
  TrivialExists.
Qed.

Theorem eval_compf:
  forall c, binary_constructor_sound (compf c) (Val.cmpf c).
Proof.
  intros; red; intros. unfold compf. TrivialExists.
Qed.

Theorem eval_compfs:
  forall c, binary_constructor_sound (compfs c) (Val.cmpfs c).
Proof.
  intros; red; intros. unfold compfs.
  replace (Val.cmpfs c x y) with
          (Val.cmpf c (Val.floatofsingle x) (Val.floatofsingle y)).
  TrivialExists. constructor. EvalOp. simpl; reflexivity.
  constructor. EvalOp. simpl; reflexivity. constructor.
  auto.
  destruct x; auto. destruct y; auto. unfold Val.cmpf, Val.cmpfs; simpl.
  rewrite Float32.cmp_double. auto.
Qed.

Theorem eval_cast8signed: unary_constructor_sound cast8signed (Val.sign_ext 8).
Proof.
  red; intros until x. unfold cast8signed. destruct (cast8signed_match a); intros.
  InvEval; TrivialExists.
  TrivialExists.
Qed.

Theorem eval_cast8unsigned: unary_constructor_sound cast8unsigned (Val.zero_ext 8).
Proof.
  red; intros. unfold cast8unsigned.
  rewrite Val.zero_ext_and. apply eval_andimm; auto. compute; auto.
Qed.

Theorem eval_cast16signed: unary_constructor_sound cast16signed (Val.sign_ext 16).
Proof.
  red; intros until x. unfold cast16signed. destruct (cast16signed_match a); intros.
  InvEval; TrivialExists.
  TrivialExists.
Qed.

Theorem eval_cast16unsigned: unary_constructor_sound cast16unsigned (Val.zero_ext 16).
Proof.
  red; intros. unfold cast16unsigned.
  rewrite Val.zero_ext_and. apply eval_andimm; auto. compute; auto.
Qed.

Theorem eval_singleoffloat: unary_constructor_sound singleoffloat Val.singleoffloat.
Proof.
  red; intros. unfold singleoffloat. TrivialExists.
Qed.

Theorem eval_floatofsingle: unary_constructor_sound floatofsingle Val.floatofsingle.
Proof.
  red; intros. unfold floatofsingle. TrivialExists.
Qed.

Theorem eval_intoffloat:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.intoffloat x = Some y ->
  exists v, eval_expr ge sp e m le (intoffloat a) v /\ Val.lessdef y v.
Proof.
  intros; unfold intoffloat. TrivialExists.
Qed.

Theorem eval_intuoffloat:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.intuoffloat x = Some y ->
  exists v, eval_expr ge sp e m le (intuoffloat a) v /\ Val.lessdef y v.
Proof.
  intros. destruct x; simpl in H0; try discriminate.
  destruct (Float.to_intu f) as [n|] eqn:?; simpl in H0; inv H0.
  exists (Vint n); split; auto. unfold intuoffloat.
  destruct Archi.ppc64.
  econstructor. constructor; eauto. constructor. simpl; rewrite Heqo; auto.
  set (im := Int.repr Int.half_modulus).
  set (fm := Float.of_intu im).
  assert (eval_expr ge sp e m (Vfloat fm :: Vfloat f :: le) (Eletvar (S O)) (Vfloat f)).
    constructor. auto.
  assert (eval_expr ge sp e m (Vfloat fm :: Vfloat f :: le) (Eletvar O) (Vfloat fm)).
    constructor. auto.
  econstructor. eauto.
  econstructor. instantiate (1 := Vfloat fm). EvalOp.
  eapply eval_Econdition with (va := Float.cmp Clt f fm).
  eauto with evalexpr.
  destruct (Float.cmp Clt f fm) eqn:?.
  exploit Float.to_intu_to_int_1; eauto. intro EQ.
  EvalOp. simpl. rewrite EQ; auto.
  exploit Float.to_intu_to_int_2; eauto.
  change Float.ox8000_0000 with im. fold fm. intro EQ.
  set (t2 := subf (Eletvar (S O)) (Eletvar O)).
  set (t3 := intoffloat t2).
  exploit (eval_subf (Vfloat fm :: Vfloat f :: le) (Eletvar (S O)) (Vfloat f) (Eletvar O)); eauto.
  fold t2. intros [v2 [A2 B2]]. simpl in B2. inv B2.
  exploit (eval_addimm Float.ox8000_0000 (Vfloat fm :: Vfloat f :: le) t3).
    unfold t3. unfold intoffloat. EvalOp. simpl. rewrite EQ. simpl. eauto.
  intros [v4 [A4 B4]]. simpl in B4. inv B4.
  rewrite Int.sub_add_opp in A4. rewrite Int.add_assoc in A4.
  rewrite (Int.add_commut (Int.neg im)) in A4.
  rewrite Int.add_neg_zero in A4.
  rewrite Int.add_zero in A4.
  auto.
Qed.

Theorem eval_floatofint:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.floatofint x = Some y ->
  exists v, eval_expr ge sp e m le (floatofint a) v /\ Val.lessdef y v.
Proof.
  intros until y. unfold floatofint. destruct (floatofint_match a); intros.
  InvEval. TrivialExists.
  destruct Archi.ppc64.
  TrivialExists.
  rename e0 into a. destruct x; simpl in H0; inv H0.
  exists (Vfloat (Float.of_int i)); split; auto.
  set (t1 := addimm Float.ox8000_0000 a).
  set (t2 := Eop Ofloatofwords (Eop (Ointconst Float.ox4330_0000) Enil ::: t1 ::: Enil)).
  set (t3 := Eop (Ofloatconst (Float.from_words Float.ox4330_0000 Float.ox8000_0000)) Enil).
  exploit (eval_addimm Float.ox8000_0000 le a). eauto. fold t1.
  intros [v1 [A1 B1]]. simpl in B1. inv B1.
  exploit (eval_subf le t2).
  unfold t2. EvalOp. constructor. EvalOp. simpl; eauto. constructor. eauto. constructor.
  unfold eval_operation. eauto.
  instantiate (2 := t3). unfold t3. EvalOp. simpl; eauto.
  intros [v2 [A2 B2]]. simpl in B2. inv B2. rewrite Float.of_int_from_words. auto.
Qed.

Theorem eval_floatofintu:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.floatofintu x = Some y ->
  exists v, eval_expr ge sp e m le (floatofintu a) v /\ Val.lessdef y v.
Proof.
  intros until y. unfold floatofintu. destruct (floatofintu_match a); intros.
  InvEval. TrivialExists.
  destruct Archi.ppc64.
  TrivialExists.
  rename e0 into a. destruct x; simpl in H0; inv H0.
  exists (Vfloat (Float.of_intu i)); split; auto.
  unfold floatofintu.
  set (t2 := Eop Ofloatofwords (Eop (Ointconst Float.ox4330_0000) Enil ::: a ::: Enil)).
  set (t3 := Eop (Ofloatconst (Float.from_words Float.ox4330_0000 Int.zero)) Enil).
  exploit (eval_subf le t2).
  unfold t2. EvalOp. constructor. EvalOp. simpl; eauto. constructor. eauto. constructor.
  unfold eval_operation. eauto.
  instantiate (2 := t3). unfold t3. EvalOp. simpl; eauto.
  intros [v2 [A2 B2]]. simpl in B2. inv B2. rewrite Float.of_intu_from_words. auto.
Qed.

Theorem eval_intofsingle:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.intofsingle x = Some y ->
  exists v, eval_expr ge sp e m le (intofsingle a) v /\ Val.lessdef y v.
Proof.
  intros; unfold intofsingle.
  assert (Val.intoffloat (Val.floatofsingle x) = Some y).
  { destruct x; simpl in H0; try discriminate.
    destruct (Float32.to_int f) eqn:F; inv H0.
    apply Float32.to_int_double in F.
    simpl. unfold Float32.to_double in F; rewrite F; auto.
  }
  apply eval_intoffloat with (Val.floatofsingle x); auto. EvalOp.
Qed.

Theorem eval_singleofint:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.singleofint x = Some y ->
  exists v, eval_expr ge sp e m le (singleofint a) v /\ Val.lessdef y v.
Proof.
  intros. unfold singleofint.
  assert (exists z, Val.floatofint x = Some z /\ y = Val.singleoffloat z).
  {
    destruct x; inv H0. simpl. exists (Vfloat (Float.of_int i)); simpl; split; auto.
    f_equal. apply Float32.of_int_double.
  }
  destruct H1 as (z & A & B). subst y.
  exploit eval_floatofint; eauto. intros (v & C & D).
  exists (Val.singleoffloat v); split. EvalOp. inv D; auto.
Qed.

Theorem eval_intuofsingle:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.intuofsingle x = Some y ->
  exists v, eval_expr ge sp e m le (intuofsingle a) v /\ Val.lessdef y v.
Proof.
  intros; unfold intuofsingle.
  assert (Val.intuoffloat (Val.floatofsingle x) = Some y).
  { destruct x; simpl in H0; try discriminate.
    destruct (Float32.to_intu f) eqn:F; inv H0.
    apply Float32.to_intu_double in F.
    simpl. unfold Float32.to_double in F; rewrite F; auto.
  }
  apply eval_intuoffloat with (Val.floatofsingle x); auto. EvalOp.
Qed.

Theorem eval_singleofintu:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.singleofintu x = Some y ->
  exists v, eval_expr ge sp e m le (singleofintu a) v /\ Val.lessdef y v.
Proof.
  intros. unfold singleofintu.
  assert (exists z, Val.floatofintu x = Some z /\ y = Val.singleoffloat z).
  {
    destruct x; inv H0. simpl. exists (Vfloat (Float.of_intu i)); simpl; split; auto.
    f_equal. apply Float32.of_intu_double.
  }
  destruct H1 as (z & A & B). subst y.
  exploit eval_floatofintu; eauto. intros (v & C & D).
  exists (Val.singleoffloat v); split. EvalOp. inv D; auto.
Qed.

Theorem eval_addressing:
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
  exists (@nil val). split. eauto with evalexpr. simpl. auto.
  exists (v1 :: nil). split. eauto with evalexpr. simpl. congruence.
  exists (v1 :: nil). split. eauto with evalexpr. simpl. congruence.
  destruct (can_use_Aindexed2 chunk).
  exists (v1 :: v0 :: nil). split. eauto with evalexpr. simpl. congruence.
  exists (Vptr b ofs :: nil). split.
  constructor. EvalOp. simpl; congruence. constructor.
  simpl. rewrite Int.add_zero. auto.
  exists (v :: nil). split. eauto with evalexpr. subst v. simpl.
  rewrite Int.add_zero. auto.
Qed.

Theorem eval_builtin_arg:
  forall a v,
  eval_expr ge sp e m nil a v ->
  CminorSel.eval_builtin_arg ge sp e m (builtin_arg a) v.
Proof.
  intros until v. unfold builtin_arg; case (builtin_arg_match a); intros; InvEval.
- constructor.
- constructor.
- constructor.
- simpl in H5. inv H5. constructor.
- subst v. constructor; auto.
- inv H. InvEval. simpl in H6; inv H6. constructor; auto.
- inv H. InvEval. simpl in H6. inv H6. constructor; auto.
- constructor; auto.
Qed.

End CMCONSTR.


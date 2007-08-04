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
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import Selection.

Open Local Scope selection_scope.

Section CMCONSTR.

Variable ge: genv.

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

Scheme eval_expr_ind_3 := Minimality for eval_expr Sort Prop
  with eval_condexpr_ind_3 := Minimality for eval_condexpr Sort Prop
  with eval_exprlist_ind_3 := Minimality for eval_exprlist Sort Prop.

Hint Resolve eval_Evar eval_Eop eval_Eload eval_Estore
             eval_Ecall eval_Econdition eval_Ealloc
             eval_Elet eval_Eletvar 
             eval_CEtrue eval_CEfalse eval_CEcond
             eval_CEcondition eval_Enil eval_Econs: evalexpr.

Lemma eval_list_one:
  forall sp le e m1 a t m2 v,
  eval_expr ge sp le e m1 a t m2 v ->
  eval_exprlist ge sp le e m1 (a ::: Enil) t m2 (v :: nil).
Proof.
  intros. econstructor. eauto. constructor. traceEq.
Qed.

Lemma eval_list_two:
  forall sp le e m1 a1 t1 m2 v1 a2 t2 m3 v2 t,
  eval_expr ge sp le e m1 a1 t1 m2 v1 ->
  eval_expr ge sp le e m2 a2 t2 m3 v2 ->
  t = t1 ** t2 ->
  eval_exprlist ge sp le e m1 (a1 ::: a2 ::: Enil) t m3 (v1 :: v2 :: nil).
Proof.
  intros. econstructor. eauto. econstructor. eauto. constructor. 
  reflexivity. traceEq.
Qed.

Lemma eval_list_three:
  forall sp le e m1 a1 t1 m2 v1 a2 t2 m3 v2 a3 t3 m4 v3 t,
  eval_expr ge sp le e m1 a1 t1 m2 v1 ->
  eval_expr ge sp le e m2 a2 t2 m3 v2 ->
  eval_expr ge sp le e m3 a3 t3 m4 v3 ->
  t = t1 ** t2 ** t3 ->
  eval_exprlist ge sp le e m1 (a1 ::: a2 ::: a3 ::: Enil) t m4 (v1 :: v2 :: v3 :: nil).
Proof.
  intros. econstructor. eauto. econstructor. eauto. econstructor. eauto. constructor. 
  reflexivity. reflexivity. traceEq.
Qed.

Hint Resolve eval_list_one eval_list_two eval_list_three: evalexpr.

Lemma eval_lift_expr:
  forall w sp le e m1 a t m2 v,
  eval_expr ge sp le e m1 a t m2 v ->
  forall p le', insert_lenv le p w le' ->
  eval_expr ge sp le' e m1 (lift_expr p a) t m2 v.
Proof.
  intros w.
  apply (eval_expr_ind_3 ge
    (fun sp le e m1 a t m2 v =>
      forall p le', insert_lenv le p w le' ->
      eval_expr ge sp le' e m1 (lift_expr p a) t m2 v)
    (fun sp le e m1 a t m2 vb =>
      forall p le', insert_lenv le p w le' ->
      eval_condexpr ge sp le' e m1 (lift_condexpr p a) t m2 vb)
    (fun sp le e m1 al t m2 vl =>
      forall p le', insert_lenv le p w le' ->
      eval_exprlist ge sp le' e m1 (lift_exprlist p al) t m2 vl));
  simpl; intros; eauto with evalexpr.

  destruct v1; eapply eval_Econdition;
  eauto with evalexpr; simpl; eauto with evalexpr.

  eapply eval_Elet. eauto. apply H2. apply insert_lenv_S; auto. auto.

  case (le_gt_dec p n); intro. 
  apply eval_Eletvar. eapply insert_lenv_lookup2; eauto.
  apply eval_Eletvar. eapply insert_lenv_lookup1; eauto.

  destruct vb1; eapply eval_CEcondition;
  eauto with evalexpr; simpl; eauto with evalexpr.
Qed.

Lemma eval_lift:
  forall sp le e m1 a t m2 v w,
  eval_expr ge sp le e m1 a t m2 v ->
  eval_expr ge sp (w::le) e m1 (lift a) t m2 v.
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

Lemma inv_eval_Eop_0:
  forall sp le e m1 op t m2 v,
  eval_expr ge sp le e m1 (Eop op Enil) t m2 v ->
  t = E0 /\ m2 = m1 /\ eval_operation ge sp op nil m1 = Some v.
Proof.
  intros. inversion H. inversion H6. 
  intuition. congruence.
Qed.
  
Lemma inv_eval_Eop_1:
  forall sp le e m1 op t a1 m2 v,
  eval_expr ge sp le e m1 (Eop op (a1 ::: Enil)) t m2 v ->
  exists v1,
  eval_expr ge sp le e m1 a1 t m2 v1 /\
  eval_operation ge sp op (v1 :: nil) m2 = Some v.
Proof.
  intros. 
  inversion H. inversion H6. inversion H18. 
  subst. exists v1; intuition. rewrite E0_right. auto.
Qed.

Lemma inv_eval_Eop_2:
  forall sp le e m1 op a1 a2 t3 m3 v,
  eval_expr ge sp le e m1 (Eop op (a1 ::: a2 ::: Enil)) t3 m3 v ->
  exists t1, exists t2, exists m2, exists v1, exists v2,
  eval_expr ge sp le e m1 a1 t1 m2 v1 /\
  eval_expr ge sp le e m2 a2 t2 m3 v2 /\
  t3 = t1 ** t2 /\
  eval_operation ge sp op (v1 :: v2 :: nil) m3 = Some v.
Proof.
  intros. 
  inversion H. subst. inversion H6. subst. inversion H8. subst.
  inversion H11. subst. 
  exists t1; exists t0; exists m0; exists v0; exists v1.
  intuition. traceEq.
Qed.

Ltac SimplEval :=
  match goal with
  | [ |- (eval_expr _ ?sp ?le ?e ?m1 (Eop ?op Enil) ?t ?m2 ?v) -> _] =>
      intro XX1;
      generalize (inv_eval_Eop_0 sp le e m1 op t m2 v XX1);
      clear XX1;
      intros [XX1 [XX2 XX3]];
      subst t m2; simpl in XX3; 
      try (simplify_eq XX3; clear XX3;
      let EQ := fresh "EQ" in (intro EQ; rewrite EQ))
  | [ |- (eval_expr _ ?sp ?le ?e ?m1 (Eop ?op (?a1 ::: Enil)) ?t ?m2 ?v) -> _] =>
      intro XX1;
      generalize (inv_eval_Eop_1 sp le e m1 op t a1 m2 v XX1);
      clear XX1;
      let v1 := fresh "v" in let EV := fresh "EV" in
      let EQ := fresh "EQ" in
      (intros [v1 [EV EQ]]; simpl in EQ)
  | [ |- (eval_expr _ ?sp ?le ?e ?m1 (Eop ?op (?a1 ::: ?a2 ::: Enil)) ?t ?m2 ?v) -> _] =>
      intro XX1;
      generalize (inv_eval_Eop_2 sp le e m1 op a1 a2 t m2 v XX1);
      clear XX1;
      let t1 := fresh "t" in let t2 := fresh "t" in
      let m := fresh "m" in
      let v1 := fresh "v" in let v2 := fresh "v" in
      let EV1 := fresh "EV" in let EV2 := fresh "EV" in
      let EQ := fresh "EQ" in let TR := fresh "TR" in
      (intros [t1 [t2 [m [v1 [v2 [EV1 [EV2 [TR EQ]]]]]]]]; simpl in EQ)
  | _ => idtac
  end.

Ltac InvEval H :=
  generalize H; SimplEval; clear H.

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

Lemma eval_notint:
  forall sp le e m1 a t m2 x,
  eval_expr ge sp le e m1 a t m2 (Vint x) ->
  eval_expr ge sp le e m1 (notint a) t m2 (Vint (Int.not x)).
Proof.
  unfold notint; intros until x; case (notint_match a); intros.
  InvEval H. FuncInv. EvalOp. simpl. congruence. 
  InvEval H. FuncInv. EvalOp. simpl. congruence. 
  InvEval H. FuncInv. EvalOp. simpl. congruence. 
  eapply eval_Elet. eexact H. 
  eapply eval_Eop.
  eapply eval_Econs. apply eval_Eletvar. simpl. reflexivity.
  eapply eval_Econs. apply eval_Eletvar. simpl. reflexivity.
  apply eval_Enil. reflexivity. reflexivity. 
  simpl. rewrite Int.or_idem. auto. traceEq.
Qed.

Lemma eval_notbool_base:
  forall sp le e m1 a t m2 v b,
  eval_expr ge sp le e m1 a t m2 v ->
  Val.bool_of_val v b ->
  eval_expr ge sp le e m1 (notbool_base a) t m2 (Val.of_bool (negb b)).
Proof. 
  TrivialOp notbool_base. simpl. 
  inversion H0. 
  rewrite Int.eq_false; auto.
  rewrite Int.eq_true; auto.
  reflexivity.
Qed.

Hint Resolve Val.bool_of_true_val Val.bool_of_false_val
             Val.bool_of_true_val_inv Val.bool_of_false_val_inv: valboolof.

Lemma eval_notbool:
  forall a sp le e m1 t m2 v b,
  eval_expr ge sp le e m1 a t m2 v ->
  Val.bool_of_val v b ->
  eval_expr ge sp le e m1 (notbool a) t m2 (Val.of_bool (negb b)).
Proof.
  assert (N1: forall v b, Val.is_false v -> Val.bool_of_val v b -> Val.is_true (Val.of_bool (negb b))).
    intros. inversion H0; simpl; auto; subst v; simpl in H.
    congruence. apply Int.one_not_zero. contradiction.
  assert (N2: forall v b, Val.is_true v -> Val.bool_of_val v b -> Val.is_false (Val.of_bool (negb b))).
    intros. inversion H0; simpl; auto; subst v; simpl in H.
    congruence. 

  induction a; simpl; intros; try (eapply eval_notbool_base; eauto).
  destruct o; try (eapply eval_notbool_base; eauto).

  destruct e. InvEval H. injection XX3; clear XX3; intro; subst v.
  inversion H0. rewrite Int.eq_false; auto. 
  simpl; eauto with evalexpr.
  rewrite Int.eq_true; simpl; eauto with evalexpr.
  eapply eval_notbool_base; eauto.

  inversion H. subst. 
  simpl in H11. eapply eval_Eop; eauto.
  simpl. caseEq (eval_condition c vl m2); intros.
  rewrite H1 in H11. 
  assert (b0 = b). 
  destruct b0; inversion H11; subst v; inversion H0; auto.
  subst b0. rewrite (Op.eval_negate_condition _ _ _ H1). 
  destruct b; reflexivity.
  rewrite H1 in H11; discriminate.

  inversion H; eauto 10 with evalexpr valboolof.
  inversion H; eauto 10 with evalexpr valboolof.

  inversion H. subst. eapply eval_Econdition with (t2 := t8). eexact H34.
  destruct v4; eauto. auto.
Qed.

Lemma eval_addimm:
  forall sp le e m1 n a t m2 x,
  eval_expr ge sp le e m1 a t m2 (Vint x) ->
  eval_expr ge sp le e m1 (addimm n a) t m2 (Vint (Int.add x n)).
Proof.
  unfold addimm; intros until x.
  generalize (Int.eq_spec n Int.zero). case (Int.eq n Int.zero); intro.
  subst n. rewrite Int.add_zero. auto.
  case (addimm_match a); intros.
  InvEval H0. EvalOp. simpl. rewrite Int.add_commut. auto.
  InvEval H0. destruct (Genv.find_symbol ge s); discriminate.
  InvEval H0. 
  destruct sp; simpl in XX3; discriminate.
  InvEval H0. FuncInv. EvalOp. simpl. subst x. 
  rewrite Int.add_assoc. decEq; decEq; decEq. apply Int.add_commut.
  EvalOp. 
Qed. 

Lemma eval_addimm_ptr:
  forall sp le e m1 n t a m2 b ofs,
  eval_expr ge sp le e m1 a t m2 (Vptr b ofs) ->
  eval_expr ge sp le e m1 (addimm n a) t m2 (Vptr b (Int.add ofs n)).
Proof.
  unfold addimm; intros until ofs.
  generalize (Int.eq_spec n Int.zero). case (Int.eq n Int.zero); intro.
  subst n. rewrite Int.add_zero. auto.
  case (addimm_match a); intros.
  InvEval H0. 
  InvEval H0. EvalOp. simpl. 
    destruct (Genv.find_symbol ge s). 
    rewrite Int.add_commut. congruence.
    discriminate.
  InvEval H0. destruct sp; simpl in XX3; try discriminate.
  inversion XX3. EvalOp. simpl. decEq. decEq. 
  rewrite Int.add_assoc. decEq. apply Int.add_commut.
  InvEval H0. FuncInv. subst b0; subst ofs. EvalOp. simpl. 
    rewrite (Int.add_commut n m). rewrite Int.add_assoc. auto.
  EvalOp. 
Qed.

Lemma eval_add:
  forall sp le e m1 a t1 m2 x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vint x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vint y) ->
  eval_expr ge sp le e m1 (add a b) (t1**t2) m3 (Vint (Int.add x y)).
Proof.
  intros until y. unfold add; case (add_match a b); intros.
  InvEval H. rewrite Int.add_commut. apply eval_addimm. 
  rewrite E0_left; assumption.
  InvEval H. FuncInv. InvEval H0. FuncInv. 
    replace (Int.add x y) with (Int.add (Int.add i i0) (Int.add n1 n2)).
    apply eval_addimm. EvalOp. 
    subst x; subst y. 
    repeat rewrite Int.add_assoc. decEq. apply Int.add_permut. 
  InvEval H. FuncInv. 
    replace (Int.add x y) with (Int.add (Int.add i y) n1).
    apply eval_addimm. EvalOp.
    subst x. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  InvEval H0. FuncInv.
    apply eval_addimm. rewrite E0_right. auto.
  InvEval H0. FuncInv. 
    replace (Int.add x y) with (Int.add (Int.add x i) n2).
    apply eval_addimm. EvalOp.
    subst y. rewrite Int.add_assoc. auto.
  EvalOp.
Qed.

Lemma eval_add_ptr:
  forall sp le e m1 a t1 m2 p x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vptr p x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vint y) ->
  eval_expr ge sp le e m1 (add a b) (t1**t2) m3 (Vptr p (Int.add x y)).
Proof.
  intros until y. unfold add; case (add_match a b); intros.
  InvEval H. 
  InvEval H. FuncInv. InvEval H0. FuncInv. 
    replace (Int.add x y) with (Int.add (Int.add i i0) (Int.add n1 n2)).
    apply eval_addimm_ptr. subst b0. EvalOp. 
    subst x; subst y.
    repeat rewrite Int.add_assoc. decEq. apply Int.add_permut. 
  InvEval H. FuncInv. 
    replace (Int.add x y) with (Int.add (Int.add i y) n1).
    apply eval_addimm_ptr. subst b0. EvalOp.
    subst x. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  InvEval H0. apply eval_addimm_ptr. rewrite E0_right. auto.
  InvEval H0. FuncInv. 
    replace (Int.add x y) with (Int.add (Int.add x i) n2).
    apply eval_addimm_ptr. EvalOp.
    subst y. rewrite Int.add_assoc. auto.
  EvalOp.
Qed.

Lemma eval_add_ptr_2:
  forall sp le e m1 a t1 m2 p x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vint x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vptr p y) ->
  eval_expr ge sp le e m1 (add a b) (t1**t2) m3 (Vptr p (Int.add y x)).
Proof.
  intros until y. unfold add; case (add_match a b); intros.
  InvEval H. 
    apply eval_addimm_ptr. rewrite E0_left. auto.
  InvEval H. FuncInv. InvEval H0. FuncInv. 
    replace (Int.add y x) with (Int.add (Int.add i0 i) (Int.add n1 n2)).
    apply eval_addimm_ptr. subst b0. EvalOp. 
    subst x; subst y.
    repeat rewrite Int.add_assoc. decEq. 
    rewrite (Int.add_commut n1 n2). apply Int.add_permut. 
  InvEval H. FuncInv. 
    replace (Int.add y x) with (Int.add (Int.add y i) n1).
    apply eval_addimm_ptr. EvalOp. 
    subst x. repeat rewrite Int.add_assoc. auto.
  InvEval H0. 
  InvEval H0. FuncInv. 
    replace (Int.add y x) with (Int.add (Int.add i x) n2).
    apply eval_addimm_ptr. EvalOp. subst b0; reflexivity.
    subst y. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  EvalOp.
Qed.

Lemma eval_sub:
  forall sp le e m1 a t1 m2 x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vint x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vint y) ->
  eval_expr ge sp le e m1 (sub a b) (t1**t2) m3 (Vint (Int.sub x y)).
Proof.
  intros until y.
  unfold sub; case (sub_match a b); intros.
  InvEval H0. rewrite Int.sub_add_opp. 
    apply eval_addimm. rewrite E0_right. assumption.
  InvEval H. FuncInv. InvEval H0. FuncInv.
    replace (Int.sub x y) with (Int.add (Int.sub i i0) (Int.sub n1 n2)).
    apply eval_addimm. EvalOp.
    subst x; subst y.
    repeat rewrite Int.sub_add_opp.
    repeat rewrite Int.add_assoc. decEq. 
    rewrite Int.add_permut. decEq. symmetry. apply Int.neg_add_distr.
  InvEval H. FuncInv. 
    replace (Int.sub x y) with (Int.add (Int.sub i y) n1).
    apply eval_addimm. EvalOp.
    subst x. rewrite Int.sub_add_l. auto.
  InvEval H0. FuncInv. 
    replace (Int.sub x y) with (Int.add (Int.sub x i) (Int.neg n2)).
    apply eval_addimm. EvalOp.
    subst y. rewrite (Int.add_commut i n2). symmetry. apply Int.sub_add_r. 
  EvalOp.
Qed.

Lemma eval_sub_ptr_int:
  forall sp le e m1 a t1 m2 p x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vptr p x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vint y) ->
  eval_expr ge sp le e m1 (sub a b) (t1**t2) m3 (Vptr p (Int.sub x y)).
Proof.
  intros until y.
  unfold sub; case (sub_match a b); intros.
  InvEval H0. rewrite Int.sub_add_opp. 
    apply eval_addimm_ptr. rewrite E0_right. assumption.
  InvEval H. FuncInv. InvEval H0. FuncInv.
    subst b0.
    replace (Int.sub x y) with (Int.add (Int.sub i i0) (Int.sub n1 n2)).
    apply eval_addimm_ptr. EvalOp.
    subst x; subst y.
    repeat rewrite Int.sub_add_opp.
    repeat rewrite Int.add_assoc. decEq. 
    rewrite Int.add_permut. decEq. symmetry. apply Int.neg_add_distr.
  InvEval H. FuncInv. subst b0.
    replace (Int.sub x y) with (Int.add (Int.sub i y) n1).
    apply eval_addimm_ptr. EvalOp.
    subst x. rewrite Int.sub_add_l. auto.
  InvEval H0. FuncInv. 
    replace (Int.sub x y) with (Int.add (Int.sub x i) (Int.neg n2)).
    apply eval_addimm_ptr. EvalOp.
    subst y. rewrite (Int.add_commut i n2). symmetry. apply Int.sub_add_r. 
  EvalOp.
Qed.

Lemma eval_sub_ptr_ptr:
  forall sp le e m1 a t1 m2 p x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vptr p x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vptr p y) ->
  eval_expr ge sp le e m1 (sub a b) (t1**t2) m3 (Vint (Int.sub x y)).
Proof.
  intros until y.
  unfold sub; case (sub_match a b); intros.
  InvEval H0. 
  InvEval H. FuncInv. InvEval H0. FuncInv.
    replace (Int.sub x y) with (Int.add (Int.sub i i0) (Int.sub n1 n2)).
    apply eval_addimm. EvalOp. 
    simpl; unfold eq_block. subst b0; subst b1; rewrite zeq_true. auto.
    subst x; subst y.
    repeat rewrite Int.sub_add_opp.
    repeat rewrite Int.add_assoc. decEq. 
    rewrite Int.add_permut. decEq. symmetry. apply Int.neg_add_distr.
  InvEval H. FuncInv. subst b0.
    replace (Int.sub x y) with (Int.add (Int.sub i y) n1).
    apply eval_addimm. EvalOp.
    simpl. unfold eq_block. rewrite zeq_true. auto.
    subst x. rewrite Int.sub_add_l. auto.
  InvEval H0. FuncInv. subst b0.
    replace (Int.sub x y) with (Int.add (Int.sub x i) (Int.neg n2)).
    apply eval_addimm. EvalOp.
    simpl. unfold eq_block. rewrite zeq_true. auto.
    subst y. rewrite (Int.add_commut i n2). symmetry. apply Int.sub_add_r. 
  EvalOp. simpl. unfold eq_block. rewrite zeq_true. auto.
Qed.

Lemma eval_rolm:
  forall sp le e m1 a amount mask t m2 x,
  eval_expr ge sp le e m1 a t m2 (Vint x) ->
  eval_expr ge sp le e m1 (rolm a amount mask) t m2 (Vint (Int.rolm x amount mask)).
Proof.
  intros until x. unfold rolm; case (rolm_match a); intros.
  InvEval H. eauto with evalexpr. 
  case (Int.is_rlw_mask (Int.and (Int.rol mask1 amount) mask)).
  InvEval H. FuncInv. EvalOp. simpl. subst x. 
  decEq. decEq. 
  replace (Int.and (Int.add amount1 amount) (Int.repr 31))
     with (Int.modu (Int.add amount1 amount) (Int.repr 32)).
  symmetry. apply Int.rolm_rolm. 
  change (Int.repr 31) with (Int.sub (Int.repr 32) Int.one).
  apply Int.modu_and with (Int.repr 5). reflexivity.
  EvalOp. 
  EvalOp.
Qed.

Lemma eval_shlimm:
  forall sp le e m1 a n t m2 x,
  eval_expr ge sp le e m1 a t m2 (Vint x) ->
  Int.ltu n (Int.repr 32) = true ->
  eval_expr ge sp le e m1 (shlimm a n) t m2 (Vint (Int.shl x n)).
Proof.
  intros.  unfold shlimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intro.
  subst n. rewrite Int.shl_zero. auto.
  rewrite H0.
  replace (Int.shl x n) with (Int.rolm x n (Int.shl Int.mone n)).
  apply eval_rolm. auto. symmetry. apply Int.shl_rolm. exact H0.
Qed.

Lemma eval_shruimm:
  forall sp le e m1 a n t m2 x,
  eval_expr ge sp le e m1 a t m2 (Vint x) ->
  Int.ltu n (Int.repr 32) = true ->
  eval_expr ge sp le e m1 (shruimm a n) t m2 (Vint (Int.shru x n)).
Proof.
  intros.  unfold shruimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intro.
  subst n. rewrite Int.shru_zero. auto.
  rewrite H0.
  replace (Int.shru x n) with (Int.rolm x (Int.sub (Int.repr 32) n) (Int.shru Int.mone n)).
  apply eval_rolm. auto. symmetry. apply Int.shru_rolm. exact H0.
Qed.

Lemma eval_mulimm_base:
  forall sp le e m1 a t n m2 x,
  eval_expr ge sp le e m1 a t m2 (Vint x) ->
  eval_expr ge sp le e m1 (mulimm_base n a) t m2 (Vint (Int.mul x n)).
Proof.
  intros; unfold mulimm_base. 
  generalize (Int.one_bits_decomp n). 
  generalize (Int.one_bits_range n).
  change (Z_of_nat wordsize) with 32.
  destruct (Int.one_bits n).
  intros. EvalOp. 
  destruct l.
  intros. rewrite H1. simpl. 
  rewrite Int.add_zero. rewrite <- Int.shl_mul.
  apply eval_shlimm. auto. auto with coqlib. 
  destruct l.
  intros. apply eval_Elet with t m2 (Vint x) E0. auto.
  rewrite H1. simpl. rewrite Int.add_zero. 
  rewrite Int.mul_add_distr_r.
  rewrite <- Int.shl_mul.
  rewrite <- Int.shl_mul.
  EvalOp. eapply eval_Econs. 
  apply eval_shlimm. apply eval_Eletvar. simpl. reflexivity. 
  auto with coqlib.
  eapply eval_Econs.
  apply eval_shlimm. apply eval_Eletvar. simpl. reflexivity.
  auto with coqlib.
  auto with evalexpr.
  reflexivity. traceEq. reflexivity. traceEq. 
  intros. EvalOp. 
Qed.

Lemma eval_mulimm:
  forall sp le e m1 a n t m2 x,
  eval_expr ge sp le e m1 a t m2 (Vint x) ->
  eval_expr ge sp le e m1 (mulimm n a) t m2 (Vint (Int.mul x n)).
Proof.
  intros until x; unfold mulimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intro.
  subst n. rewrite Int.mul_zero. 
  intro. eapply eval_Elet; eauto with evalexpr. traceEq.
  generalize (Int.eq_spec n Int.one); case (Int.eq n Int.one); intro.
  subst n. rewrite Int.mul_one. auto.
  case (mulimm_match a); intros.
  InvEval H1. EvalOp. rewrite Int.mul_commut. reflexivity.
  InvEval H1. FuncInv. 
  replace (Int.mul x n) with (Int.add (Int.mul i n) (Int.mul n n2)).
  apply eval_addimm. apply eval_mulimm_base. auto.
  subst x. rewrite Int.mul_add_distr_l. decEq. apply Int.mul_commut.
  apply eval_mulimm_base. assumption.
Qed.

Lemma eval_mul:
  forall sp le e m1 a t1 m2 x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vint x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vint y) ->
  eval_expr ge sp le e m1 (mul a b) (t1**t2) m3 (Vint (Int.mul x y)).
Proof.
  intros until y.
  unfold mul; case (mul_match a b); intros.
  InvEval H. rewrite Int.mul_commut. apply eval_mulimm. 
  rewrite E0_left; auto.
  InvEval H0. rewrite E0_right. apply eval_mulimm. auto.
  EvalOp.
Qed.

Lemma eval_divs:
  forall sp le e m1 a t1 m2 x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vint x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vint y) ->
  y <> Int.zero ->
  eval_expr ge sp le e m1 (divs a b) (t1**t2) m3 (Vint (Int.divs x y)).
Proof.
  TrivialOp divs. simpl. 
  predSpec Int.eq Int.eq_spec y Int.zero. contradiction. auto.
Qed.

Lemma eval_mod_aux:
  forall divop semdivop,
  (forall sp x y m,
   y <> Int.zero ->
   eval_operation ge sp divop (Vint x :: Vint y :: nil) m =
   Some (Vint (semdivop x y))) ->
  forall sp le e m1 a t1 m2 x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vint x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vint y) ->
  y <> Int.zero ->
  eval_expr ge sp le e m1 (mod_aux divop a b) (t1**t2) m3
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
  apply eval_Enil. reflexivity. reflexivity. 
  apply H. assumption.
  eapply eval_Econs. apply eval_Eletvar. simpl; reflexivity.
  apply eval_Enil. reflexivity. reflexivity. 
  simpl; reflexivity. apply eval_Enil. 
  reflexivity. reflexivity. reflexivity.
  reflexivity. traceEq.
Qed.

Lemma eval_mods:
  forall sp le e m1 a t1 m2 x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vint x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vint y) ->
  y <> Int.zero ->
  eval_expr ge sp le e m1 (mods a b) (t1**t2) m3 (Vint (Int.mods x y)).
Proof.
  intros; unfold mods. 
  rewrite Int.mods_divs. 
  eapply eval_mod_aux; eauto. 
  intros. simpl. predSpec Int.eq Int.eq_spec y0 Int.zero. 
  contradiction. auto.
Qed.

Lemma eval_divu_base:
  forall sp le e m1 a t1 m2 x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vint x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vint y) ->
  y <> Int.zero ->
  eval_expr ge sp le e m1 (Eop Odivu (a ::: b ::: Enil)) (t1**t2) m3 (Vint (Int.divu x y)).
Proof.
  intros. EvalOp. simpl. 
  predSpec Int.eq Int.eq_spec y Int.zero. contradiction. auto.
Qed.

Lemma eval_divu:
  forall sp le e m1 a t1 m2 x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vint x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vint y) ->
  y <> Int.zero ->
  eval_expr ge sp le e m1 (divu a b) (t1**t2) m3 (Vint (Int.divu x y)).
Proof.
  intros until y.
  unfold divu; case (divu_match b); intros.
  InvEval H0. caseEq (Int.is_power2 y). 
  intros. rewrite (Int.divu_pow2 x y i H0).
  apply eval_shruimm. rewrite E0_right. auto.
  apply Int.is_power2_range with y. auto.
  intros. subst n2. eapply eval_divu_base. eexact H. EvalOp. auto.
  eapply eval_divu_base; eauto.
Qed.

Lemma eval_modu:
  forall sp le e m1 a t1 m2 x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vint x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vint y) ->
  y <> Int.zero ->
  eval_expr ge sp le e m1 (modu a b) (t1**t2) m3 (Vint (Int.modu x y)).
Proof.
  intros until y; unfold modu; case (divu_match b); intros.
  InvEval H0. caseEq (Int.is_power2 y). 
  intros. rewrite (Int.modu_and x y i H0).
  rewrite <- Int.rolm_zero. apply eval_rolm. rewrite E0_right; auto.
  intro. rewrite Int.modu_divu. eapply eval_mod_aux. 
  intros. simpl. predSpec Int.eq Int.eq_spec y0 Int.zero.
  contradiction. auto.
  eexact H. EvalOp. auto. auto.
  rewrite Int.modu_divu. eapply eval_mod_aux. 
  intros. simpl. predSpec Int.eq Int.eq_spec y0 Int.zero.
  contradiction. auto.
  eexact H. eexact H0. auto. auto.
Qed.

Lemma eval_andimm:
  forall sp le e m1 n a t m2 x,
  eval_expr ge sp le e m1 a t m2 (Vint x) ->
  eval_expr ge sp le e m1 (andimm n a) t m2 (Vint (Int.and x n)).
Proof.
  intros.  unfold andimm. case (Int.is_rlw_mask n).
  rewrite <- Int.rolm_zero. apply eval_rolm; auto.
  EvalOp. 
Qed.

Lemma eval_and:
  forall sp le e m1 a t1 m2 x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vint x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vint y) ->
  eval_expr ge sp le e m1 (and a b) (t1**t2) m3 (Vint (Int.and x y)).
Proof.
  intros until y; unfold and; case (mul_match a b); intros.
  InvEval H. rewrite Int.and_commut. 
  rewrite E0_left; apply eval_andimm; auto.
  InvEval H0. rewrite E0_right; apply eval_andimm; auto.
  EvalOp.
Qed.

Remark eval_same_expr_pure:
  forall a1 a2 sp le e m1 t1 m2 v1 t2 m3 v2,
  same_expr_pure a1 a2 = true ->
  eval_expr ge sp le e m1 a1 t1 m2 v1 ->
  eval_expr ge sp le e m2 a2 t2 m3 v2 ->
  t1 = E0 /\ t2 = E0 /\ a2 = a1 /\ v2 = v1 /\ m2 = m1.
Proof.
  intros until v2.
  destruct a1; simpl; try (intros; discriminate). 
  destruct a2; simpl; try (intros; discriminate).
  case (ident_eq i i0); intros.
  subst i0. inversion H0. inversion H1. 
  assert (v2 = v1). congruence. tauto.
  discriminate.
Qed.

Lemma eval_or:
  forall sp le e m1 a t1 m2 x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vint x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vint y) ->
  eval_expr ge sp le e m1 (or a b) (t1**t2) m3 (Vint (Int.or x y)).
Proof.
  intros until y; unfold or; case (or_match a b); intros.
  generalize (Int.eq_spec amount1 amount2); case (Int.eq amount1 amount2); intro.
  case (Int.is_rlw_mask (Int.or mask1 mask2)).
  caseEq (same_expr_pure t0 t3); intro.
  simpl. InvEval H. FuncInv. InvEval H0. FuncInv. 
  generalize (eval_same_expr_pure _ _ _ _ _ _ _ _ _ _ _ _ H2 EV EV0).
  intros [EQ1 [EQ2 [EQ3 [EQ4 EQ5]]]]. 
  injection EQ4; intro EQ7. subst.
  EvalOp. simpl. rewrite Int.or_rolm. auto.
  simpl. EvalOp. 
  simpl. EvalOp. 
  simpl. EvalOp. 
  EvalOp.
Qed.

Lemma eval_shl:
  forall sp le e m1 a t1 m2 x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vint x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vint y) ->
  Int.ltu y (Int.repr 32) = true ->
  eval_expr ge sp le e m1 (shl a b) (t1**t2) m3 (Vint (Int.shl x y)).
Proof.
  intros until y; unfold shl; case (shift_match b); intros.
  InvEval H0. rewrite E0_right. apply eval_shlimm; auto.
  EvalOp. simpl. rewrite H1. auto.
Qed.

Lemma eval_shru:
  forall sp le e m1 a t1 m2 x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vint x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vint y) ->
  Int.ltu y (Int.repr 32) = true ->
  eval_expr ge sp le e m1 (shru a b) (t1**t2) m3 (Vint (Int.shru x y)).
Proof.
  intros until y; unfold shru; case (shift_match b); intros.
  InvEval H0. rewrite E0_right; apply eval_shruimm; auto.
  EvalOp. simpl. rewrite H1. auto.
Qed.

Lemma eval_addf:
  forall sp le e m1 a t1 m2 x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vfloat x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vfloat y) ->
  eval_expr ge sp le e m1 (addf a b) (t1**t2) m3 (Vfloat (Float.add x y)).
Proof.
  intros until y; unfold addf; case (addf_match a b); intros.
  InvEval H. FuncInv. EvalOp. 
  econstructor; eauto. econstructor; eauto. econstructor; eauto. constructor.
  traceEq. simpl. subst x. reflexivity.
  InvEval H0. FuncInv. eapply eval_Elet. eexact H. EvalOp. 
  econstructor; eauto with evalexpr. 
  econstructor; eauto with evalexpr. 
  econstructor. apply eval_Eletvar. simpl; reflexivity.
  constructor. reflexivity. traceEq.
  subst y. rewrite Float.addf_commut. reflexivity. auto.
  EvalOp.
Qed.
 
Lemma eval_subf:
  forall sp le e m1 a t1 m2 x b t2 m3 y,
  eval_expr ge sp le e m1 a t1 m2 (Vfloat x) ->
  eval_expr ge sp le e m2 b t2 m3 (Vfloat y) ->
  eval_expr ge sp le e m1 (subf a b) (t1**t2) m3 (Vfloat (Float.sub x y)).
Proof.
  intros until y; unfold subf; case (subf_match a b); intros.
  InvEval H. FuncInv. EvalOp. 
  econstructor; eauto. econstructor; eauto. econstructor; eauto. constructor.
  traceEq. subst x. reflexivity.
  EvalOp.
Qed.

Lemma eval_cast8signed:
  forall sp le e m1 a t m2 v,
  eval_expr ge sp le e m1 a t m2 v ->
  eval_expr ge sp le e m1 (cast8signed a) t m2 (Val.cast8signed v).
Proof. 
  intros until v; unfold cast8signed; case (cast8signed_match a); intros.
  replace (Val.cast8signed v) with v. auto. 
  InvEval H. inversion EQ. destruct v0; simpl; auto. rewrite Int.cast8_signed_idem. reflexivity.
  EvalOp.
Qed.

Lemma eval_cast8unsigned:
  forall sp le e m1 a t m2 v,
  eval_expr ge sp le e m1 a t m2 v ->
  eval_expr ge sp le e m1 (cast8unsigned a) t m2 (Val.cast8unsigned v).
Proof. 
  intros until v; unfold cast8unsigned; case (cast8unsigned_match a); intros.
  replace (Val.cast8unsigned v) with v. auto. 
  InvEval H. inversion EQ. destruct v0; simpl; auto. rewrite Int.cast8_unsigned_idem. reflexivity.
  EvalOp.
Qed.

Lemma eval_cast16signed:
  forall sp le e m1 a t m2 v,
  eval_expr ge sp le e m1 a t m2 v ->
  eval_expr ge sp le e m1 (cast16signed a) t m2 (Val.cast16signed v).
Proof. 
  intros until v; unfold cast16signed; case (cast16signed_match a); intros.
  replace (Val.cast16signed v) with v. auto. 
  InvEval H. inversion EQ. destruct v0; simpl; auto. rewrite Int.cast16_signed_idem. reflexivity.
  EvalOp.
Qed.

Lemma eval_cast16unsigned:
  forall sp le e m1 a t m2 v,
  eval_expr ge sp le e m1 a t m2 v ->
  eval_expr ge sp le e m1 (cast16unsigned a) t m2 (Val.cast16unsigned v).
Proof. 
  intros until v; unfold cast16unsigned; case (cast16unsigned_match a); intros.
  replace (Val.cast16unsigned v) with v. auto. 
  InvEval H. inversion EQ. destruct v0; simpl; auto. rewrite Int.cast16_unsigned_idem. reflexivity.
  EvalOp.
Qed.

Lemma eval_singleoffloat:
  forall sp le e m1 a t m2 v,
  eval_expr ge sp le e m1 a t m2 v ->
  eval_expr ge sp le e m1 (singleoffloat a) t m2 (Val.singleoffloat v).
Proof. 
  intros until v; unfold singleoffloat; case (singleoffloat_match a); intros.
  replace (Val.singleoffloat v) with v. auto. 
  InvEval H. inversion EQ. destruct v0; simpl; auto. rewrite Float.singleoffloat_idem. reflexivity.
  EvalOp.
Qed.

Lemma eval_base_condition_of_expr:
  forall sp le a e m1 t m2 v (b: bool),
  eval_expr ge sp le e m1 a t m2 v ->
  Val.bool_of_val v b ->
  eval_condexpr ge sp le e m1 
                (CEcond (Ccompimm Cne Int.zero) (a ::: Enil))
                t m2 b.
Proof.
  intros. 
  eapply eval_CEcond. eauto with evalexpr. 
  inversion H0; simpl. rewrite Int.eq_false; auto. auto. auto.
Qed.

Lemma eval_condition_of_expr:
  forall a sp le e m1 t m2 v (b: bool),
  eval_expr ge sp le e m1 a t m2 v ->
  Val.bool_of_val v b ->
  eval_condexpr ge sp le e m1 (condexpr_of_expr a) t m2 b.
Proof.
  induction a; simpl; intros;
    try (eapply eval_base_condition_of_expr; eauto; fail).
  destruct o; try (eapply eval_base_condition_of_expr; eauto; fail).

  destruct e. InvEval H. inversion XX3; subst v.
  inversion H0. 
  rewrite Int.eq_false; auto. constructor.
  subst i; rewrite Int.eq_true. constructor.
  eapply eval_base_condition_of_expr; eauto.

  inversion H. subst. eapply eval_CEcond; eauto. simpl in H11.
  destruct (eval_condition c vl); try discriminate.
  destruct b0; inversion H11; subst; inversion H0; congruence.

  inversion H. subst.
  destruct v1; eauto with evalexpr.
Qed.

Lemma eval_addressing:
  forall sp le e m1 a t m2 v b ofs,
  eval_expr ge sp le e m1 a t m2 v ->
  v = Vptr b ofs ->
  match addressing a with (mode, args) =>
    exists vl,
    eval_exprlist ge sp le e m1 args t m2 vl /\ 
    eval_addressing ge sp mode vl = Some v
  end.
Proof.
  intros until v. unfold addressing; case (addressing_match a); intros.
  InvEval H. exists (@nil val). split. eauto with evalexpr. 
  simpl. auto.
  InvEval H. exists (@nil val). split. eauto with evalexpr. 
  simpl. auto.
  InvEval H. InvEval EV. rewrite E0_left in TR. subst t1. FuncInv. 
    congruence.
    destruct (Genv.find_symbol ge s); congruence.
    exists (Vint i0 :: nil). split. eauto with evalexpr. 
    simpl. subst v. destruct (Genv.find_symbol ge s). congruence.
    discriminate.
  InvEval H. FuncInv. 
    congruence.
    exists (Vptr b0 i :: nil). split. eauto with evalexpr. 
    simpl. congruence.
  InvEval H. FuncInv. 
    congruence.
    exists (Vint i :: Vptr b0 i0 :: nil).
    split. eauto with evalexpr. simpl. 
    rewrite Int.add_commut. congruence.
    exists (Vptr b0 i :: Vint i0 :: nil).
    split. eauto with evalexpr. simpl. congruence.
  exists (v :: nil). split. eauto with evalexpr. 
    subst v. simpl. rewrite Int.add_zero. auto.
Qed.

Lemma eval_load:
  forall sp le e m1 a t m2 v chunk v',
  eval_expr ge sp le e m1 a t m2 v ->
  Mem.loadv chunk m2 v = Some v' ->
  eval_expr ge sp le e m1 (load chunk a) t m2 v'.
Proof.
  intros. generalize H0; destruct v; simpl; intro; try discriminate.
  unfold load. 
  generalize (eval_addressing _ _ _ _ _ _ _ _ _ _ H (refl_equal _)).
  destruct (addressing a). intros [vl [EV EQ]]. 
  eapply eval_Eload; eauto. 
Qed.

Lemma eval_store:
  forall sp le e m1 a1 t1 m2 v1 a2 t2 m3 v2 chunk m4,
  eval_expr ge sp le e m1 a1 t1 m2 v1 ->
  eval_expr ge sp le e m2 a2 t2 m3 v2 ->
  Mem.storev chunk m3 v1 v2 = Some m4 ->
  eval_expr ge sp le e m1 (store chunk a1 a2) (t1**t2) m4 v2.
Proof.
  intros. generalize H1; destruct v1; simpl; intro; try discriminate.
  unfold store.
  generalize (eval_addressing _ _ _ _ _ _ _ _ _ _ H (refl_equal _)).
  destruct (addressing a1). intros [vl [EV EQ]]. 
  eapply eval_Estore; eauto. 
Qed.

(** * Correctness of instruction selection for operators *)

(** We now prove a semantic preservation result for the [sel_unop]
  and [sel_binop] selection functions.  The proof exploits
  the results of the previous section. *)

Lemma eval_sel_unop:
  forall sp le e m op a1 t m1 v1 v,
  eval_expr ge sp le e m a1 t m1 v1 ->
  eval_unop op v1 = Some v ->
  eval_expr ge sp le e m (sel_unop op a1) t m1 v.
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
Qed.

Lemma eval_sel_binop:
  forall sp le e m op a1 a2 t1 m1 v1 t2 m2 v2 v,
  eval_expr ge sp le e m a1 t1 m1 v1 ->
  eval_expr ge sp le e m1 a2 t2 m2 v2 ->
  eval_binop op v1 v2 m2 = Some v ->
  eval_expr ge sp le e m (sel_binop op a1 a2) (t1 ** t2) m2 v.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  eapply eval_add; eauto.
  eapply eval_add_ptr_2; eauto.
  eapply eval_add_ptr; eauto.
  eapply eval_sub; eauto.
  eapply eval_sub_ptr_int; eauto.
  destruct (eq_block b b0); inv H1. 
  eapply eval_sub_ptr_ptr; eauto.
  eapply eval_mul; eauto.
  generalize (Int.eq_spec i0 Int.zero). intro. destruct (Int.eq i0 Int.zero); inv H1.
  eapply eval_divs; eauto.
  generalize (Int.eq_spec i0 Int.zero). intro. destruct (Int.eq i0 Int.zero); inv H1.
  eapply eval_divu; eauto.
  generalize (Int.eq_spec i0 Int.zero). intro. destruct (Int.eq i0 Int.zero); inv H1.
  eapply eval_mods; eauto.
  generalize (Int.eq_spec i0 Int.zero). intro. destruct (Int.eq i0 Int.zero); inv H1.
  eapply eval_modu; eauto.
  eapply eval_and; eauto.
  eapply eval_or; eauto.
  EvalOp.
  caseEq (Int.ltu i0 (Int.repr 32)); intro; rewrite H2 in H1; inv H1.
  eapply eval_shl; eauto.
  EvalOp.
  caseEq (Int.ltu i0 (Int.repr 32)); intro; rewrite H2 in H1; inv H1.
  eapply eval_shru; eauto.
  eapply eval_addf; eauto.
  eapply eval_subf; eauto.
  EvalOp.
  EvalOp.
  EvalOp. simpl. destruct (Int.cmp c i i0); auto. 
  EvalOp. simpl. generalize H1; unfold eval_compare_null, Cminor.eval_compare_null.
  destruct (Int.eq i Int.zero). destruct c; intro EQ; inv EQ; auto.
  auto.
  EvalOp. simpl. generalize H1; unfold eval_compare_null, Cminor.eval_compare_null.
  destruct (Int.eq i0 Int.zero). destruct c; intro EQ; inv EQ; auto.
  auto.
  EvalOp. simpl. 
  destruct (valid_pointer m2 b (Int.signed i) && valid_pointer m2 b0 (Int.signed i0)).
  destruct (eq_block b b0); inv H1. 
  destruct (Int.cmp c i i0); auto.
  auto.
  EvalOp. simpl. destruct (Int.cmpu c i i0); auto.
  EvalOp. simpl. destruct (Float.cmp c f f0); auto.
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

(** This is the main semantic preservation theorem:
  instruction selection preserves the semantics of function invocations.
  The proof is an induction over the Cminor evaluation derivation. *)

Lemma sel_function_correct:
  forall m fd vargs t m' vres,
  Cminor.eval_funcall ge m fd vargs t m' vres ->
  CminorSel.eval_funcall tge m (sel_fundef fd) vargs t m' vres.
Proof.
  apply (Cminor.eval_funcall_ind4 ge
          (fun sp le e m a t m' v => eval_expr tge sp le e m (sel_expr a) t m' v)
          (fun sp le e m a t m' v => eval_exprlist tge sp le e m (sel_exprlist a) t m' v)
          (fun m fd vargs t m' vres => eval_funcall tge m (sel_fundef fd) vargs t m' vres)
          (fun sp e m s t e' m' out => exec_stmt tge sp e m (sel_stmt s) t e' m' out));
  intros; simpl.
  (* Evar *)
  constructor; auto.
  (* Econst *)
  destruct cst; simpl; simpl in H; (econstructor; [constructor|simpl;auto]).
  rewrite symbols_preserved. auto.
  (* Eunop *)
  eapply eval_sel_unop; eauto.
  (* Ebinop *)
  subst t. eapply eval_sel_binop; eauto.
  (* Eload *)
  eapply eval_load; eauto.
  (* Estore *)
  subst t. eapply eval_store; eauto.
  (* Ecall *)
  econstructor; eauto. apply functions_translated; auto.
  rewrite <- H4. apply sig_function_translated.
  (* Econdition *)
  econstructor; eauto. eapply eval_condition_of_expr; eauto. 
  destruct b1; auto.
  (* Elet *)
  econstructor; eauto.
  (* Eletvar *)
  constructor; auto.
  (* Ealloc *)
  econstructor; eauto.
  (* Enil *)
  constructor.
  (* Econs *)
  econstructor; eauto.
  (* Internal function *)
  econstructor; eauto. 
  (* External function *)
  econstructor; eauto.
  (* Sskip *)
  constructor.
  (* Sexpr *)
  econstructor; eauto.
  (* Sassign *)
  econstructor; eauto.
  (* Sifthenelse *)
  econstructor; eauto. eapply eval_condition_of_expr; eauto.
  destruct b1; auto.
  (* Sseq *)
  eapply exec_Sseq_continue; eauto.
  eapply exec_Sseq_stop; eauto.
  (* Sloop *)
  eapply exec_Sloop_loop; eauto.
  eapply exec_Sloop_stop; eauto.
  (* Sblock *)
  econstructor; eauto.
  (* Sexit *)
  constructor.
  (* Sswitch *)
  econstructor; eauto.
  (* Sreturn *)
  constructor.
  econstructor; eauto.
  (* Stailcall *)
  econstructor; eauto. apply functions_translated; auto.
  rewrite <- H4. apply sig_function_translated.
Qed.

End PRESERVATION.

(** As a corollary, instruction selection preserves the observable
   behaviour of programs. *)

Theorem sel_program_correct:
  forall prog t r,
  Cminor.exec_program prog t r ->
  CminorSel.exec_program (sel_program prog) t r.
Proof.
  intros.
  destruct H as [b [f [m [FINDS [FINDF [SIG EXEC]]]]]].
  exists b; exists (sel_fundef f); exists m.
  split. simpl. rewrite <- FINDS. apply symbols_preserved.
  split. apply function_ptr_translated. auto.
  split. rewrite <- SIG. apply sig_function_translated. 
  replace (Genv.init_mem (sel_program prog)) with (Genv.init_mem prog).
  apply sel_function_correct; auto.
  symmetry. unfold sel_program. apply Genv.init_mem_transf.
Qed.

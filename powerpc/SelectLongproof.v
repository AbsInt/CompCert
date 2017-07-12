(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                 Xavier Leroy, INRIA Paris                           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness of instruction selection for 64-bit integer operations *)

Require Import String Coqlib Maps Integers Floats Errors.
Require Archi.
Require Import AST Values Memory Globalenvs Events.
Require Import Cminor Op CminorSel.
Require Import SelectOp SelectOpproof SplitLong SplitLongproof.
Require Import SelectLong.

Local Open Scope cminorsel_scope.
Local Open Scope string_scope.

(** * Correctness of the instruction selection functions for 64-bit operators *)

Section CMCONSTR.

Variable prog: program.
Variable hf: helper_functions.
Hypothesis HELPERS: helper_functions_declared prog hf.
Let ge := Genv.globalenv prog.
Variable sp: val.
Variable e: env.
Variable m: mem.

Definition unary_constructor_sound (cstr: expr -> expr) (sem: val -> val) : Prop :=
  forall le a x,
  eval_expr ge sp e m le a x ->
  exists v, eval_expr ge sp e m le (cstr a) v /\ Val.lessdef (sem x) v.

Definition binary_constructor_sound (cstr: expr -> expr -> expr) (sem: val -> val -> val) : Prop :=
  forall le a x b y,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  exists v, eval_expr ge sp e m le (cstr a b) v /\ Val.lessdef (sem x y) v.

Definition partial_unary_constructor_sound (cstr: expr -> expr) (sem: val -> option val) : Prop :=
  forall le a x y,
  eval_expr ge sp e m le a x ->
  sem x = Some y ->
  exists v, eval_expr ge sp e m le (cstr a) v /\ Val.lessdef y v.

Definition partial_binary_constructor_sound (cstr: expr -> expr -> expr) (sem: val -> val -> option val) : Prop :=
  forall le a x b y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  sem x y = Some z ->
  exists v, eval_expr ge sp e m le (cstr a b) v /\ Val.lessdef z v.

Theorem eval_longconst:
  forall le n, eval_expr ge sp e m le (longconst n) (Vlong n).
Proof.
  unfold longconst; intros; destruct Archi.splitlong.
  apply SplitLongproof.eval_longconst.
  EvalOp.
Qed.

Lemma is_longconst_sound:
  forall v a n le,
  is_longconst a = Some n -> eval_expr ge sp e m le a v -> v = Vlong n.
Proof with (try discriminate).
  intros. unfold is_longconst in *. destruct Archi.splitlong.
  eapply SplitLongproof.is_longconst_sound; eauto.
  assert (a = Eop (Olongconst n) Enil).
  { destruct a... destruct o... destruct e0... congruence. }
  subst a. InvEval. auto.
Qed.

Theorem eval_intoflong: unary_constructor_sound intoflong Val.loword.
Proof.
  unfold intoflong; destruct Archi.splitlong. apply SplitLongproof.eval_intoflong.
  red; intros. destruct (is_longconst a) as [n|] eqn:C.
- TrivialExists. simpl. erewrite (is_longconst_sound x) by eauto. auto.
- TrivialExists.
Qed.

Theorem eval_longofintu: unary_constructor_sound longofintu Val.longofintu.
Proof.
  unfold longofintu; destruct Archi.splitlong. apply SplitLongproof.eval_longofintu.
  red; intros. destruct (is_intconst a) as [n|] eqn:C.
- econstructor; split. apply eval_longconst.
  exploit is_intconst_sound; eauto. intros; subst x. auto.
- TrivialExists.
Qed.

Theorem eval_longofint: unary_constructor_sound longofint Val.longofint.
Proof.
  unfold longofint; destruct Archi.splitlong. apply SplitLongproof.eval_longofint.
  red; intros. destruct (is_intconst a) as [n|] eqn:C.
- econstructor; split. apply eval_longconst.
  exploit is_intconst_sound; eauto. intros; subst x. auto.
- TrivialExists.
Qed.

Theorem eval_notl: unary_constructor_sound notl Val.notl.
Proof.
  unfold notl; destruct Archi.splitlong. apply SplitLongproof.eval_notl.
  red; intros. destruct (notl_match a).
- InvEval. econstructor; split. apply eval_longconst. auto.
- InvEval. subst. exists v1; split; auto. destruct v1; simpl; auto. rewrite Int64.not_involutive; auto.
- TrivialExists.
Qed.

Theorem eval_andlimm: forall n, unary_constructor_sound (andlimm n) (fun v => Val.andl v (Vlong n)).
Proof.
  unfold andlimm; intros; red; intros.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
  exists (Vlong Int64.zero); split. apply eval_longconst.
  subst. destruct x; simpl; auto. rewrite Int64.and_zero; auto.
  predSpec Int64.eq Int64.eq_spec n Int64.mone.
  exists x; split. assumption.
  subst. destruct x; simpl; auto. rewrite Int64.and_mone; auto.
  destruct (andlimm_match a); InvEval; subst.
- econstructor; split. apply eval_longconst. simpl. rewrite Int64.and_commut; auto.
- TrivialExists. simpl. rewrite Val.andl_assoc. rewrite Int64.and_commut; auto.
- TrivialExists. simpl. destruct v1; simpl; auto. unfold Int64.rolm. rewrite Int64.and_assoc.
  rewrite  (Int64.and_commut mask2 n). reflexivity.
- TrivialExists.
Qed.

Theorem eval_andl: binary_constructor_sound andl Val.andl.
Proof.
  unfold andl; destruct Archi.splitlong. apply SplitLongproof.eval_andl.
  red; intros. destruct (andl_match a b).
- InvEval. rewrite Val.andl_commut. apply eval_andlimm; auto.
- InvEval. apply eval_andlimm; auto.
- TrivialExists.
Qed.

Theorem eval_orlimm: forall n, unary_constructor_sound (orlimm n) (fun v => Val.orl v (Vlong n)).
Proof.
  unfold orlimm; intros; red; intros.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
  exists x; split; auto. subst. destruct x; simpl; auto. rewrite Int64.or_zero; auto.
  predSpec Int64.eq Int64.eq_spec n Int64.mone.
  econstructor; split. apply eval_longconst. subst. destruct x; simpl; auto. rewrite Int64.or_mone; auto.
  destruct (orlimm_match a); InvEval; subst.
- econstructor; split. apply eval_longconst. simpl. rewrite Int64.or_commut; auto.
- TrivialExists. simpl. rewrite Val.orl_assoc. rewrite Int64.or_commut; auto.
- TrivialExists.
Qed.

Theorem eval_orl: binary_constructor_sound orl Val.orl.
Proof.
  unfold orl; destruct Archi.splitlong. apply SplitLongproof.eval_orl.
  red; intros.
  assert (DEFAULT: exists v, eval_expr ge sp e m le (Eop Oorl (a:::b:::Enil)) v /\ Val.lessdef (Val.orl x y) v) by TrivialExists.
  assert (ROLM: forall v n1 n2 m1 m2,
             n1 = n2 ->
             Val.lessdef (Val.orl (Val.rolml v n1 m1) (Val.rolml v n2 m2))
                         (Val.rolml v n1 (Int64.or m1 m2))).
  { intros. destruct v; simpl; auto. unfold Int64.rolm.
    rewrite Int64.and_or_distrib. rewrite H1. auto. }
  destruct (orl_match a b).
- predSpec Int.eq Int.eq_spec amount1 amount2; simpl.
   destruct (same_expr_pure t1 t2) eqn:?; auto. InvEval.
   exploit eval_same_expr; eauto. intros [EQ1 EQ2]; subst.
   exists (Val.rolml v0 amount2 (Int64.or mask1 mask2)); split. EvalOp.
   apply ROLM; auto. auto.
- InvEval. rewrite Val.orl_commut. apply eval_orlimm; auto.
- InvEval. apply eval_orlimm; auto.
- apply DEFAULT.
Qed.

Theorem eval_xorlimm: forall n, unary_constructor_sound (xorlimm n) (fun v => Val.xorl v (Vlong n)).
Proof.
  unfold xorlimm; intros; red; intros.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
  exists x; split; auto. subst. destruct x; simpl; auto. rewrite Int64.xor_zero; auto.
  predSpec Int64.eq Int64.eq_spec n Int64.mone.
  replace (Val.xorl x (Vlong n)) with (Val.notl x). apply eval_notl; auto.
  subst n. destruct x; simpl; auto.
  destruct (xorlimm_match a); InvEval; subst.
- econstructor; split. apply eval_longconst. simpl. rewrite Int64.xor_commut; auto.
- TrivialExists. simpl. rewrite Val.xorl_assoc. rewrite Int64.xor_commut; auto.
- TrivialExists. simpl. destruct v1; simpl; auto. unfold Int64.not.
  rewrite Int64.xor_assoc. apply f_equal. apply f_equal. apply f_equal.
  apply Int64.xor_commut.
- TrivialExists.
Qed.

Theorem eval_xorl: binary_constructor_sound xorl Val.xorl.
Proof.
  unfold xorl; destruct Archi.splitlong. apply SplitLongproof.eval_xorl.
  red; intros. destruct (xorl_match a b).
- InvEval. rewrite Val.xorl_commut. apply eval_xorlimm; auto.
- InvEval. apply eval_xorlimm; auto.
- TrivialExists.
Qed.

Theorem eval_rolml: forall amount mask, unary_constructor_sound (fun v => rolml v amount mask) (fun v => Val.rolml v amount mask).
Proof.
  unfold rolml. intros; red; intros.
  predSpec Int.eq Int.eq_spec amount Int.zero.
  rewrite H0.
  exploit (eval_andlimm). eauto. intros (x0 & (H1 & H2)).
  exists x0. split. apply H1. destruct x; auto. simpl. unfold Int64.rolm.
  change (Int64.repr (Int.unsigned Int.zero)) with Int64.zero. rewrite Int64.rol_zero.
  apply H2.
  destruct (rolml_match a).
- econstructor; split. apply eval_longconst. simpl. InvEval. unfold Val.rolml. auto.
- InvEval. TrivialExists. simpl. rewrite <- H. 
  unfold Val.rolml; destruct v1; simpl; auto.
  rewrite Int64.rolm_rolm by (exists (two_p (64-6)); auto).
  f_equal. f_equal. f_equal.
  unfold Int64.add. rewrite ! Int64.int_unsigned_repr. unfold Int.add. 
  set (a := Int.unsigned amount1 + Int.unsigned amount).
  unfold Int.modu, Int64.modu. 
  change (Int.unsigned Int64.iwordsize') with 64.
  change (Int64.unsigned Int64.iwordsize) with 64.
  f_equal.
  rewrite Int.unsigned_repr. 
  apply Int.eqmod_mod_eq. omega. 
  apply Int.eqmod_trans with a.
  apply Int.eqmod_divides with Int.modulus. apply Int.eqm_sym. apply Int.eqm_unsigned_repr.
  exists (two_p (32-6)); auto.
  apply Int.eqmod_divides with Int64.modulus. apply Int64.eqm_unsigned_repr.
  exists (two_p (64-6)); auto.
  assert (0 <= Int.unsigned (Int.repr a) mod 64 < 64) by (apply Z_mod_lt; omega).
  assert (64 < Int.max_unsigned) by (compute; auto).
  omega.
- InvEval. TrivialExists. simpl. rewrite <- H.
  unfold Val.rolml; destruct v1; simpl; auto. unfold Int64.rolm.
  rewrite Int64.rol_and. rewrite Int64.and_assoc. auto.
- TrivialExists.
Qed.

Theorem eval_shllimm: forall n, unary_constructor_sound (fun e => shllimm e n) (fun v => Val.shll v (Vint n)).
Proof.
  intros; unfold shllimm. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_shllimm; auto.
  red; intros.
  predSpec Int.eq Int.eq_spec n Int.zero.
  exists x; split; auto. subst n; destruct x; simpl; auto.
  destruct (Int.ltu Int.zero Int64.iwordsize'); auto.
  change (Int64.shl' i Int.zero) with (Int64.shl i Int64.zero). rewrite Int64.shl_zero; auto.
  destruct (Int.ltu n Int64.iwordsize') eqn:LT; simpl.
- rewrite Val.shll_rolml by apply LT. apply eval_rolml. auto.
- TrivialExists. constructor; eauto.  constructor. EvalOp. simpl; eauto. constructor.
  constructor.
Qed.

Theorem eval_shrluimm: forall n, unary_constructor_sound (fun e => shrluimm e n) (fun v => Val.shrlu v (Vint n)).
Proof.
  unfold shrluimm; destruct Archi.splitlong. apply SplitLongproof.eval_shrluimm. auto.
  red; intros.
  predSpec Int.eq Int.eq_spec n Int.zero.
  exists x. split. apply H. destruct x; simpl; auto. rewrite H0. rewrite Int64.shru'_zero. constructor.
  destruct (Int.ltu n Int64.iwordsize') eqn:LT; simpl.
- rewrite Val.shrlu_rolml by apply LT. apply eval_rolml. auto.
- TrivialExists. constructor; eauto.  constructor. EvalOp. simpl; eauto. constructor.
  constructor.
Qed.

Theorem eval_shrlimm: forall n, unary_constructor_sound (fun e => shrlimm e n) (fun v => Val.shrl v (Vint n)).
Proof.
  intros; unfold shrlimm. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_shrlimm; auto.
  red; intros.
  predSpec Int.eq Int.eq_spec n Int.zero.
  exists x; split; auto. subst n; destruct x; simpl; auto.
  destruct (Int.ltu Int.zero Int64.iwordsize'); auto.
  change (Int64.shr' i Int.zero) with (Int64.shr i Int64.zero). rewrite Int64.shr_zero; auto.
  destruct (Int.ltu n Int64.iwordsize') eqn:LT; simpl.
  assert (DEFAULT: exists v, eval_expr ge sp e m le (Eop (Oshrlimm n) (a:::Enil)) v
                         /\  Val.lessdef (Val.shrl x (Vint n)) v) by TrivialExists.
  destruct (shrlimm_match a); InvEval.
- TrivialExists. simpl; rewrite LT; auto.
- destruct (Int.ltu (Int.add n n1) Int64.iwordsize') eqn:LT'; auto.
  subst. econstructor; split. EvalOp. simpl; eauto.
  destruct v1; simpl; auto. rewrite LT'.
  destruct (Int.ltu n1 Int64.iwordsize') eqn:LT1; auto.
  simpl; rewrite LT. rewrite Int.add_commut, Int64.shr'_shr'; auto. rewrite Int.add_commut; auto.
- apply DEFAULT.
- TrivialExists. constructor; eauto. constructor. EvalOp. simpl; eauto. constructor. auto.
Qed.

Theorem eval_shll: binary_constructor_sound shll Val.shll.
Proof.
  unfold shll. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_shll; auto.
  red; intros. destruct (is_intconst b) as [n2|] eqn:C.
- exploit is_intconst_sound; eauto. intros EQ; subst y. apply eval_shllimm; auto.
- TrivialExists.
Qed.

Theorem eval_shrlu: binary_constructor_sound shrlu Val.shrlu.
Proof.
  unfold shrlu. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_shrlu; auto.
  red; intros. destruct (is_intconst b) as [n2|] eqn:C.
- exploit is_intconst_sound; eauto. intros EQ; subst y. apply eval_shrluimm; auto.
- TrivialExists.
Qed.

Theorem eval_shrl: binary_constructor_sound shrl Val.shrl.
Proof.
  unfold shrl. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_shrl; auto.
  red; intros. destruct (is_intconst b) as [n2|] eqn:C.
- exploit is_intconst_sound; eauto. intros EQ; subst y. apply eval_shrlimm; auto.
- TrivialExists.
Qed.

Theorem eval_negl: unary_constructor_sound negl Val.negl.
Proof.
  unfold negl. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_negl; auto.
  red; intros. destruct (is_longconst a) as [n|] eqn:C.
- exploit is_longconst_sound; eauto. intros EQ; subst x.
  econstructor; split. apply eval_longconst. auto.
- TrivialExists.
Qed.

Theorem eval_addlimm: forall n, unary_constructor_sound (addlimm n) (fun v => Val.addl v (Vlong n)).
Proof.
  unfold addlimm.
  red; intros. predSpec Int64.eq Int64.eq_spec n Int64.zero.
  exists x. split; auto. rewrite H0. destruct x; auto. simpl. rewrite Int64.add_zero. constructor.
  destruct (addlimm_match a).
- econstructor; split. apply eval_longconst. simpl. InvEval. unfold Val.rolml. auto.
- InvEval. TrivialExists. simpl. rewrite <- H. rewrite Val.addl_assoc. reflexivity.
- InvEval. TrivialExists.
Qed.


Theorem eval_addl: binary_constructor_sound addl Val.addl.
Proof.
  unfold addl. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_addl; auto.
  red; intros. destruct (addl_match a b); InvEval; subst.
- exploit (eval_addlimm n1); eauto. intros (n & (H1 & H2)). exists n. split; auto.
  rewrite Val.addl_commut. exact H2.
- exploit (eval_addlimm n2). apply H. auto.
- rewrite Val.addl_permut_4. simpl.
  apply eval_addlimm; EvalOp.
- rewrite Val.addl_assoc. rewrite Val.addl_permut. rewrite Val.addl_commut.
  apply eval_addlimm; EvalOp.
- rewrite Val.addl_commut. rewrite Val.addl_assoc. rewrite Val.addl_permut.
  rewrite Val.addl_commut. apply eval_addlimm; EvalOp. rewrite Val.addl_commut.
  constructor.
- TrivialExists.
Qed.

Theorem eval_subl: binary_constructor_sound subl Val.subl.
Proof.
  unfold subl. destruct Archi.splitlong eqn:SL.
  apply SplitLongproof.eval_subl. apply Archi.splitlong_ptr32; auto.
  red; intros; destruct (subl_match a b); InvEval.
- rewrite Val.subl_addl_opp. apply eval_addlimm; auto.
-  TrivialExists.
Qed.

Theorem eval_mullimm_base: forall n, unary_constructor_sound (mullimm_base n) (fun v => Val.mull v (Vlong n)).
Proof.
  intros; unfold mullimm_base. red. intros.
  assert (DEFAULT: exists v : val, eval_expr ge sp e m le (Eop Omull (a ::: longconst n ::: Enil)) v
                              /\ Val.lessdef (Val.mull x (Vlong n)) v).
  { TrivialExists. constructor. eauto. constructor. apply eval_longconst. constructor. auto. }
  generalize (Int64.one_bits'_decomp n); intros D.
  destruct (Int64.one_bits' n) as [ | i [ | j [ | ? ? ]]] eqn:B; auto.
- replace (Val.mull x (Vlong n)) with (Val.shll x (Vint i)).
  apply eval_shllimm; auto.
  simpl in D. rewrite D, Int64.add_zero. destruct x; simpl; auto.
  rewrite (Int64.one_bits'_range n) by (rewrite B; auto with coqlib).
  rewrite Int64.shl'_mul; auto.
- set (le' := x :: le).
  assert (A0: eval_expr ge sp e m le' (Eletvar O) x) by (constructor; reflexivity).
  exploit (eval_shllimm i). eexact A0. intros (v1 & A1 & B1).
  exploit (eval_shllimm j). eexact A0. intros (v2 & A2 & B2).
  exploit (eval_addl). eexact A1. eexact A2. intros (v3 & A3 & B3).
  exists v3; split. econstructor; eauto.
  rewrite D. simpl. rewrite Int64.add_zero. destruct x; auto.
  simpl in *.
  rewrite (Int64.one_bits'_range n) in B1 by (rewrite B; auto with coqlib).
  rewrite (Int64.one_bits'_range n) in B2 by (rewrite B; auto with coqlib).
  inv B1; inv B2. simpl in B3; inv B3.
  rewrite Int64.mul_add_distr_r. rewrite <- ! Int64.shl'_mul. auto.
Qed.

Theorem eval_mullimm: forall n, unary_constructor_sound (mullimm n) (fun v => Val.mull v (Vlong n)).
Proof.
  unfold mullimm. intros.
  destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_mullimm; eauto.
  red; intros. predSpec Int64.eq Int64.eq_spec n Int64.zero.
  exists (Vlong Int64.zero).
  split. apply eval_longconst. destruct x; simpl; auto.
  subst n; rewrite Int64.mul_zero; auto.
  predSpec Int64.eq Int64.eq_spec n Int64.one.
  exists x; split; auto.
  destruct x; simpl; auto. subst n; rewrite Int64.mul_one; auto.
  destruct (mullimm_match a); InvEval.
- econstructor; split. apply eval_longconst. rewrite Int64.mul_commut; auto.
- exploit (eval_mullimm_base n); eauto.
Qed.

Theorem eval_mull: binary_constructor_sound mull Val.mull.
Proof.
  unfold mull. destruct Archi.splitlong eqn:SL.
  apply SplitLongproof.eval_mull; auto.
  red; intros. destruct (mull_match a b).
- exploit (eval_mullimm n1); eauto. intros (n & (H1 & H2)). InvEval. exists n. split; auto.
  rewrite Val.mull_commut. exact H2.
- exploit (eval_mullimm n2). apply H. InvEval. auto.
- TrivialExists.
Qed.

Theorem eval_mullhu:
  forall n, unary_constructor_sound (fun a => mullhu a n) (fun v => Val.mullhu v (Vlong n)).
Proof.
  unfold mullhu; intros. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_mullhu; auto.
  red; intros. TrivialExists. constructor. eauto. constructor. apply eval_longconst. constructor. auto.
Qed.

Theorem eval_mullhs:
  forall n, unary_constructor_sound (fun a => mullhs a n) (fun v => Val.mullhs v (Vlong n)).
Proof.
  unfold mullhs; intros. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_mullhs; auto.
  red; intros. TrivialExists. constructor. eauto. constructor. apply eval_longconst. constructor. auto.
Qed.

Theorem eval_shrxlimm:
  forall le a n x z,
  eval_expr ge sp e m le a x ->
  Val.shrxl x (Vint n) = Some z ->
  exists v, eval_expr ge sp e m le (shrxlimm a n) v /\ Val.lessdef z v.
Proof.
  unfold shrxlimm. intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_shrxlimm; eauto.
  predSpec Int.eq Int.eq_spec n Int.zero.
- subst n. destruct x; simpl in H0; inv H0. econstructor; split; eauto.
  change (Int.ltu Int.zero (Int.repr 63)) with true. simpl. rewrite Int64.shrx'_zero; auto.
- TrivialExists.
Qed.

Theorem eval_divls_base: partial_binary_constructor_sound divls_base Val.divls.
Proof.
  unfold divls_base; red; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_divls_base; eauto.
  TrivialExists.
Qed.

Lemma eval_modl_aux:
  forall divop semdivop,
  (forall sp x y m, eval_operation ge sp divop (x :: y :: nil) m = semdivop x y) ->
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  semdivop x y = Some z ->
  eval_expr ge sp e m le (modl_aux divop a b) (Val.subl x (Val.mull z y)).
Proof.
  intros; unfold modl_aux.
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

Theorem eval_modls_base: partial_binary_constructor_sound modls_base Val.modls.
Proof.
  unfold modls_base. red; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_modls_base; eauto.
  assert (DEFAULT: exists v : val, eval_expr ge sp e m le (modl_aux Odivl a b) v /\ Val.lessdef z v).
  exploit Val.modls_divls; eauto. intros [v [A B]].
  { subst. econstructor; split; eauto.
    apply eval_modl_aux with (semdivop := Val.divls); auto. }

  destruct (is_longconst a) as [n1|] eqn:A. exploit is_longconst_sound. eauto. eauto. intros.
  destruct (is_longconst b) as [n2|] eqn:B; auto. exploit is_longconst_sound. eauto. eauto. intros.
  predSpec Int64.eq Int64.eq_spec Int64.zero n2; simpl.
  (* n1 mod n2, n2 = 0 *)
  auto.
  predSpec Int64.eq Int64.eq_spec n1 (Int64.repr Int64.min_signed); predSpec Int64.eq Int64.eq_spec n2 Int64.mone; simpl; auto; subst.
- (* signed_min mod n2 | n2 != 0, n2 !- =1 *)
  econstructor; split. apply eval_longconst.
  unfold Val.modls in H1.
  rewrite Int64.eq_false in H1; auto.
  rewrite (Int64.eq_false n2 Int64.mone H6) in H1.
  inversion H1. auto.
- (* n1 mod -1, n1 !- signed_min *)
  econstructor; split. apply eval_longconst.
  unfold Val.modls in H1.
  rewrite Int64.eq_false in H1; auto.
  rewrite Int64.eq_false in H1; auto.
  inversion H1. auto.
- (* other valid cases *)
  econstructor; split. apply eval_longconst.
  unfold Val.modls in H1.
  rewrite Int64.eq_false in H1; auto.
  rewrite Int64.eq_false in H1; auto.
  inversion H1.
  auto.
- (* fallback *)
  apply DEFAULT.
Qed.


Theorem eval_divlu_base: partial_binary_constructor_sound divlu_base Val.divlu.
Proof.
  unfold divlu_base; red; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_divlu_base; eauto.
  TrivialExists.
Qed.

Theorem eval_modlu_base: partial_binary_constructor_sound modlu_base Val.modlu.
Proof.
  unfold modlu_base; red; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_modlu_base; eauto.
  assert (DEFAULT: exists v : val, eval_expr ge sp e m le (modl_aux Odivlu a b) v /\ Val.lessdef z v).
  exploit Val.modlu_divlu; eauto. intros [v [A B]].
  subst. econstructor; split; eauto.
  apply eval_modl_aux with (semdivop := Val.divlu); auto.
  (* n1 and n2 are longconsts *)
  destruct (is_longconst a) as [n1|] eqn:A. exploit is_longconst_sound; eauto.
  destruct (is_longconst b) as [n2|] eqn:B; auto. exploit is_longconst_sound; eauto. intros.
  predSpec Int64.eq Int64.eq_spec Int64.zero n2; simpl.
  (* n2 = 0 *)
-  auto.
  (* n2 != 0 *)
-  econstructor; split. apply eval_longconst.
  rewrite H2 in H1.
  rewrite H3 in H1.
  unfold Val.modlu in H1.
  rewrite Int64.eq_false in H1; auto.
  inversion H1. auto.
-  (* n1 no longconst, n2 is longconst *)
  destruct (is_longconst b) as [n2|] eqn:B; auto. exploit is_longconst_sound; eauto. intros.
  destruct (Int64.is_power2 n2) eqn:C; auto.
  (* n2 is power of 2 *)
  exploit eval_andlimm. apply H. intros. destruct H3.
  exists x0.  split. apply H3.
  replace z with (Val.andl x (Vlong (Int64.sub n2 Int64.one))). apply H3.
  apply (Val.modlu_pow2 x n2 i z); congruence.
Qed.

Theorem eval_cmplu:
  forall c le a x b y v,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.cmplu (Mem.valid_pointer m) c x y = Some v ->
  eval_expr ge sp e m le (cmplu c a b) v.
Proof.
  unfold cmplu; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_cmplu; eauto using Archi.splitlong_ptr32.
  unfold Val.cmplu in H1.
  destruct (Val.cmplu_bool (Mem.valid_pointer m) c x y) as [vb|] eqn:C; simpl in H1; inv H1.
  destruct (is_longconst a) as [n1|] eqn:LC1; destruct (is_longconst b) as [n2|] eqn:LC2;
  try (assert (x = Vlong n1) by (eapply is_longconst_sound; eauto));
  try (assert (y = Vlong n2) by (eapply is_longconst_sound; eauto));
  subst.
- simpl in C; inv C. EvalOp. destruct (Int64.cmpu c n1 n2); reflexivity.
- EvalOp. simpl. rewrite Val.swap_cmplu_bool. rewrite C; auto.
- EvalOp. simpl; rewrite C; auto.
- EvalOp. simpl; rewrite C; auto.
Qed.

Theorem eval_cmpl:
  forall c le a x b y v,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.cmpl c x y = Some v ->
  eval_expr ge sp e m le (cmpl c a b) v.
Proof.
  unfold cmpl; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_cmpl; eauto.
  unfold Val.cmpl in H1.
  destruct (Val.cmpl_bool c x y) as [vb|] eqn:C; simpl in H1; inv H1.
  destruct (is_longconst a) as [n1|] eqn:LC1; destruct (is_longconst b) as [n2|] eqn:LC2;
  try (assert (x = Vlong n1) by (eapply is_longconst_sound; eauto));
  try (assert (y = Vlong n2) by (eapply is_longconst_sound; eauto));
  subst.
- simpl in C; inv C. EvalOp. destruct (Int64.cmp c n1 n2); reflexivity.
- EvalOp. simpl. rewrite Val.swap_cmpl_bool. rewrite C; auto.
- EvalOp. simpl; rewrite C; auto.
- EvalOp. simpl; rewrite C; auto.
Qed.

Theorem eval_longoffloat:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.longoffloat x = Some y ->
  exists v, eval_expr ge sp e m le (longoffloat a) v /\ Val.lessdef y v.
Proof.
  unfold longoffloat. intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_longoffloat; eauto.
  TrivialExists.
Qed.

Theorem eval_floatoflong:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.floatoflong x = Some y ->
  exists v, eval_expr ge sp e m le (floatoflong a) v /\ Val.lessdef y v.
Proof.
  unfold floatoflong. intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_floatoflong; eauto.
  TrivialExists.
Qed.

Theorem eval_longofsingle:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.longofsingle x = Some y ->
  exists v, eval_expr ge sp e m le (longofsingle a) v /\ Val.lessdef y v.
Proof.
  intros; unfold longofsingle.
  destruct x; simpl in H0; inv H0. destruct (Float32.to_long f) as [n|] eqn:EQ; simpl in H2; inv H2.
  exploit eval_floatofsingle; eauto. intros (v & A & B). simpl in B. inv B.
  apply Float32.to_long_double in EQ.
  eapply eval_longoffloat; eauto. simpl.
  change (Float.of_single f) with (Float32.to_double f); rewrite EQ; auto.
Qed.

End CMCONSTR.
